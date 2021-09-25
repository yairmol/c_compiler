open Parser;;
(* #use "parser.ml";; *)
(* #use "typeCheck.ml";; *)

(*
an expression is assignable if
1. it is a variable
2. it is an Accessor or Index of an assignable
*)

(* TODO: identify constant expressions - expressions that can be calculated at compile time *)
(* an expression is contant if 
  1. 
*)

(* semantic analysis to make:
1. Constant idenification
2. variable lexical addressing
3. variable accesses
4. collect variable declarations in functions
5. boxing?

 contant *)

type expression' =
  | Const of const
  | FreeVar of string
  | BoundVar of bool * int * int * string (* (is_param, major_index, minor_index, name) *)
  | FuncCall of expression' * expression' list
  | PreUnaryExpression of string * expression'
  | PostUnrayExpression of expression' * string
  | BinaryExpresion of string * expression' * expression'
  | TernaryExpression of expression' * expression' * expression'
  | Accessor of expression' * string
  | Index of expression' * expression';;

type statement' =
  | IfStatement of expression' * statement' list * statement' list option
  | ForStatement of (statement' * statement' * statement') * statement' list
  | FuncDecStatement of 
      type_expr * string * 
      (string * type_expr) list * 
      (string * type_expr) list *
      statement' list option
  | VariableDec of type_expr * (string * expression' option) list
  | Assignment of expression' * expression'
  | ExprStatement of expression'
  | ReturnStatement of expression'
  | TypedefStatement of type_expr * string
  | StructDec of string option * statement' list;;

(* TODO: identify compund constants and dynamic constants *)
(* 
A compund Literal is a constant if
*)

(* let validate_functions funcs typedefs structdefs globals =
  let funcdec_to_func = 1;
  List.map
  (function
    | FuncDecStatement   *)
open List;;

let apply2 f (x, y) =
  (f x, f y);;

let apply3 f (x, y, z) =
  (f x, f y, f z);;

let option_to_list = function
  | None -> []
  | Some l -> l

let collect_var_decl (funcbody: statement list) = 
  let rec collect_var_decl (stmt: statement) = match stmt with
    | IfStatement (test, then_stmts, else_stmts) -> 
        List.concat 
          ((List.map collect_var_decl then_stmts)@
           (List.map collect_var_decl (option_to_list else_stmts)))
    
    | ForStatement (head, body) -> 
        let (vd1, vd2, vd3) = apply3 collect_var_decl head in
        List.concat ([vd1; vd2; vd3]@(List.map collect_var_decl body))

    | VariableDec (t, vars) -> List.map (fun (name, _) -> (name, t)) vars
    
    | _ -> []
  in List.concat (List.map collect_var_decl funcbody);;

(* let globals = TypeCheck.create_variable_lookup_table stmts in *)
let create_variable_lookup_table stmts = List.concat (List.filter_map
  (fun (stmt: statement) -> match stmt with
    | FuncDecStatement (ret_t, name, params, body) -> 
        Some [(name, (TFunc (ret_t, List.map (fun (t, n) -> t) params), false, -1, -1))]
    | VariableDec (t, names_and_vals) -> 
        Some (List.map (fun (name, v) -> (name, (t, false, -1, -1))) names_and_vals)
    | _ -> None) stmts);;

let update_variable_lookup_table (params: (string * type_expr) list) locals varlu =
  (List.mapi (fun i (n, t) -> (n, (t, true, 0, i))) params)@
  (List.mapi (fun i (n, t) -> (n, (t, false, 0, i))) locals)@
  (List.map (fun (n, (t, _, maji, mini)) -> (n, (t, false, maji + 1, mini))) varlu);;

let semantic_analysis stmts =
  let e_to_e' varlu =
    let rec e_to_e' (expr: expression) = match expr with
      | Const c -> Const c
      
      | Var v -> (match (List.assoc_opt v varlu) with
        | None -> FreeVar v
        | Some (t, is_param, maji, mini) -> BoundVar (is_param, maji, mini, v))
      
      | FuncCall (e, es) -> FuncCall (e_to_e' e, List.map e_to_e' es)

      | PostUnrayExpression (e, op) -> PostUnrayExpression (e_to_e' e, op)

      | PreUnaryExpression (op, e) -> PreUnaryExpression (op, e_to_e' e)

      | BinaryExpresion (op, e1, e2) -> BinaryExpresion (op, e_to_e' e1, e_to_e' e2)

      | TernaryExpression (e1, e2, e3) -> TernaryExpression (e_to_e' e1, e_to_e' e2, e_to_e' e3)

      | Accessor (e, member) -> Accessor (e_to_e' e, member)

      | Index (e1, e2) -> Index (e_to_e' e1, e_to_e' e2)
  in e_to_e' in

  let rec s_to_s' varlu (stmt: statement) : statement' = match stmt with
    | IfStatement (test, then_stmts, else_stmts) -> 
        let s_to_s' = s_to_s' varlu in
        IfStatement (
          e_to_e' varlu test,
          map s_to_s' then_stmts,
          Option.map (map s_to_s') else_stmts
        )

    | ForStatement (head, body) -> 
        let s_to_s' = s_to_s' varlu in
        ForStatement (apply3 s_to_s' head, map s_to_s' body)

    | FuncDecStatement (ret_t, name, params, body) -> 
        let locals = collect_var_decl (option_to_list body) in
        let params = List.map (fun (t, n) -> (n, t)) params in
        let varlu = update_variable_lookup_table params locals varlu in
        let s_to_s' = s_to_s' varlu in
        FuncDecStatement (
          ret_t, name,
          params,
          locals,
          Option.map (List.map s_to_s') body
        )
    
    | VariableDec (t, names_and_vals) -> 
        let e_to_e' = Option.map (e_to_e' varlu) in
        VariableDec (t, List.map (fun (n, v) -> (n, e_to_e' v)) names_and_vals)
    | Assignment (e1, e2) -> Assignment (e_to_e' varlu e1, e_to_e' varlu e2)
    | ExprStatement e -> ExprStatement (e_to_e' varlu e)
    | ReturnStatement e -> ReturnStatement (e_to_e' varlu e)
    | TypedefStatement (t, n) -> TypedefStatement (t, n)
    | StructDec (name, mems) -> StructDec (name, List.map (s_to_s' varlu) mems)
  in List.map (s_to_s' []) stmts;;