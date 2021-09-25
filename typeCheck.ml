open Parser;;
(* #use "parser.ml" *)

exception TypeError of string;;
exception SemanticError of string;;

let base_types = [
  ("int", TInt);
  ("float", TFloat);
  ("char", TChar);
  ("double", TDouble);
  ("void", TVoid)
];;

let parse_struct_members members = List.concat (List.map
  (function
    | VariableDec (t, names_and_vals) -> List.map (fun (name, v) -> (name, t)) names_and_vals
    | _ -> raise (SemanticError "only member declaration is allowed when declaring a struct"))
  members)

let create_type_lookup_table stmts = 
  base_types@(List.filter_map
    (function
      | TypedefStatement (t, name) -> Some (name, t)
      | StructDec (Some name, members) -> Some (name, TStruct (parse_struct_members members))
      | _ -> None) stmts);;

let create_variable_lookup_table stmts = List.concat (List.filter_map
  (function
    | FuncDecStatement (ret_t, name, params, body) -> 
        Some [(name, TFunc (ret_t, List.map (fun (t, n) -> t) params))]
    | VariableDec (t, names_and_vals) -> 
        Some (List.map (fun (name, v) -> (name, t)) names_and_vals)
    | _ -> None) stmts);;

let type_eq type_lookup =
  let rec type_eq t1 t2 = if t1 = t2 then true else match (t1, t2) with
    | (TPointer t1, TPointer t2) -> (type_eq t1 t2)
    | (TArr (t1, size1), TArr (t2, size2)) -> size1 = size2 && (type_eq t1 t2)
    | (TFunc (ret_t1, params_t1), TFunc (ret_t2, params_t2)) -> 
        List.for_all (fun (t1, t2) -> (type_eq t1 t2)) (List.combine (ret_t1 :: params_t1) (ret_t2 :: params_t2))
    | (Unkn name, t2) -> (match (List.assoc_opt name type_lookup) with
      | Some t -> (type_eq t t2)
      | None -> raise (TypeError "unknown type"))
    | (t1, Unkn name) -> (match (List.assoc_opt name type_lookup) with
      | Some t -> (type_eq t1 t)
      | None -> raise (TypeError "unknown type"))
    | _, _ -> false
  in type_eq;;

let expr_type typelu varlu =
  let type_eq = type_eq typelu in
  let rec expr_type expr = match expr with
    | Const c -> (match c with
      | Int n -> TInt
      | Chr c -> TChar
      | Flt f -> TFloat
      | Str s -> TPointer TChar)

    | Var v -> (match List.assoc_opt v varlu with
      | Some t -> t
      | None -> raise (SemanticError "unknown variable"))

    | FuncCall (ef, args) -> (match (expr_type ef) with
      | TFunc (ret_t, params_t) -> 
          if (List.for_all 
              (fun (param_t, arg_t) -> 
                (type_eq param_t arg_t)) 
              (List.combine
                params_t 
                (List.map expr_type args)))
          then ret_t
          else raise (TypeError "args types mismatch in function call")
      | _ -> raise (TypeError "expression is not callable"))

    | PreUnaryExpression (_, e) -> expr_type e

    | PostUnrayExpression (e, _) -> expr_type e

    | BinaryExpresion (_, e1, e2) -> 
        let (t1, t2) = (expr_type e1, expr_type e2) in
        if (type_eq t1 t2) 
        then t1
        else raise (TypeError "unmatching operands types")

    | TernaryExpression (test, thn, els) -> 
        let (t1, t2) = (expr_type thn, expr_type els) in
        if (type_eq t1 t2)
        then t1 
        else raise (TypeError "unmatching types for the then and else parts of a ternary expression")

    | Accessor (e, mem_name) -> (match (expr_type e) with
      | TStruct members -> (match (List.assoc_opt mem_name members) with
        | Some t -> t
        | None -> raise (TypeError "no such member for struct"))
      | _ -> raise (TypeError "only structs can be accessed"))

    | Index (indexed, index) -> let (t_indexed, t_index) = (expr_type indexed, expr_type index) in
      if (type_eq t_index TInt)
      then (match t_indexed with
        | TPointer t -> t 
        | TArr (t, size) -> t
        | _ -> raise (TypeError "an indexed expression must be of type pointer"))
      else raise (TypeError "the index expression in [] must be an integer")
  in expr_type;;

let type_check stmts =
  (* this will check the type of an expression. if all types within the subexpressions are matching
    then the type of the expression will be return. otherwise an exception will be thrown *)
  let type_lookup = create_type_lookup_table stmts in
  
  let var_lookup = create_variable_lookup_table stmts in
  
  let stmts = List.filter (function
    | VariableDec _ -> false
    | StructDec _ -> false
    | TypedefStatement _ -> false
    | _ -> true) stmts in
  
  let rec type_check type_lookup var_lookup stmts = match stmts with
    | [] -> true
    | stmt :: stmts -> match stmt with
      | IfStatement (expression, then_stmts, else_stmts) -> 
          let type_check = (type_check type_lookup var_lookup) in
          (type_check then_stmts) && (type_check stmts)

      | ForStatement ((s1, s2, s3), body) -> 
          let type_check = (type_check type_lookup var_lookup) in
          (type_check ([s1; s2; s3]@body)) && (type_check stmts)

      | FuncDecStatement (t, name, params, body) -> (match body with
          | Some body ->
            let func_var_lookup = (List.map (fun (t, name) -> (name, t)) params)@var_lookup in
            (type_check type_lookup func_var_lookup body)
            && (type_check type_lookup var_lookup stmts)
          | None -> (type_check type_lookup var_lookup stmts))

      | VariableDec (t, names_and_vals) ->
          (List.for_all
            (function
             | (_, Some v) -> (type_eq type_lookup (expr_type type_lookup var_lookup v) t)
             | (_, None) -> true)
            names_and_vals) &&
          let var_lookup = (List.map (fun (name, v) -> (name, t)) names_and_vals)@var_lookup in
          (type_check type_lookup var_lookup stmts)

      | Assignment (e1, e2) -> 
          (type_eq type_lookup 
            (expr_type type_lookup var_lookup e1)
            (expr_type type_lookup var_lookup e2))
          && (type_check type_lookup var_lookup stmts)

      | ExprStatement e -> 
          ((expr_type type_lookup var_lookup e); true)
          && (type_check type_lookup var_lookup stmts)

      | ReturnStatement e -> 
          ((expr_type type_lookup var_lookup e); true)
          && (type_check type_lookup var_lookup stmts)
          
      | TypedefStatement (t, name) -> type_check ((name, t) :: type_lookup) var_lookup stmts

      | StructDec (Some name, members) -> 
          type_check 
            ((name, TStruct (parse_struct_members members)) :: type_lookup)
            var_lookup
            stmts

      | StructDec (None, members) -> type_check type_lookup var_lookup stmts
  in type_check type_lookup var_lookup stmts;;

let resolve_typedefs stmts =
  
  let type_lookup = create_type_lookup_table stmts in
  
  let stmts = List.filter (function
    | StructDec _ -> false
    | TypedefStatement _ -> false
    | _ -> true) stmts in
  
  let resolve_type typelu =
    let rec resolve_type = function
      | TPointer t -> TPointer (resolve_type t)
      | TArr (t, size) -> TArr (resolve_type t, size)
      | TFunc (ret_t, params_t) -> TFunc (resolve_type ret_t, List.map resolve_type params_t)
      | Unkn name -> (match (List.assoc_opt name typelu) with
        | Some t -> resolve_type t
        | None -> raise (TypeError "unknown type"))
      | TStruct members -> TStruct (List.map (fun (name, t) -> (name, resolve_type t)) members)
      | t -> t
  in resolve_type in
  
  let rec resolve_typedefs typelu stmts =
    match stmts with
    | [] -> []
    | stmt :: stmts -> match stmt with
      | IfStatement (test, then_stmts, else_stmts) -> (IfStatement (
          test,
          resolve_typedefs typelu then_stmts,
          (match else_stmts with
            | None -> None
            | Some else_stmts -> Some (resolve_typedefs typelu else_stmts))
        )) :: (resolve_typedefs typelu stmts)

    | ForStatement ((s1, s2, s3), body) -> (ForStatement (
        (List.nth (resolve_typedefs typelu [s1]) 0,
         List.nth (resolve_typedefs typelu [s2]) 0,
         List.nth (resolve_typedefs typelu [s3]) 0),
         resolve_typedefs typelu body
      )) :: (resolve_typedefs typelu stmts)

    | FuncDecStatement (ret_t, name, params, body) -> 
        let resolve_params = List.map (fun (t, name) -> (resolve_type typelu t, name)) params in
        (FuncDecStatement (
          resolve_type typelu ret_t,
          name,
          resolve_params,
          (match body with
            | Some body -> Some (resolve_typedefs typelu body)
            | None -> None)
        )) :: (resolve_typedefs typelu stmts)
    
    | VariableDec (t, names_and_vals) -> (VariableDec (
        resolve_type typelu t, names_and_vals
      )) :: (resolve_typedefs typelu stmts)
    
    | TypedefStatement (t, name) -> (TypedefStatement (t, name)) ::
        (resolve_typedefs ((name, t) :: typelu) stmts)
    
    | StructDec (Some name, members) -> (StructDec (Some name, resolve_typedefs typelu members)) ::
        (resolve_typedefs ((name, TStruct (parse_struct_members members)) :: typelu) stmts)
    
    | stmt -> stmt :: (resolve_typedefs typelu stmts) in
    
    resolve_typedefs type_lookup stmts;;