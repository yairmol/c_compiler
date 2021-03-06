open Pc;;
(* #use "pc.ml";; *)

exception ParserError of string;;

type const = 
  | Int of int
  | Chr of char
  | Str of string
  | Flt of float;;
  (* | CompundLiteral of const list;; *)

(* int parser *)

let char_to_digit ch = (int_of_char ch) - (int_of_char '0');;

let int_nt =
  (PC.disj
    (PC.packaten
      (PC.range '1' '9')
      (PC.star (PC.range '0' '9'))
      (fun (dig1, digits) -> 
        List.fold_left 
          (fun num dig -> (num * 10) + (char_to_digit dig))
          (char_to_digit dig1)
          digits))
    (PC.pack (PC.char '0') (fun _ -> 0)));;

(* float parser *)

let char_to_float ch = float_of_int (char_to_digit ch);;

let float_nt = 
  (PC.packaten
    (PC.caten int_nt (PC.char '.'))
    (PC.pack 
      (PC.plus (PC.range '0' '9'))
      (fun digits -> 
        List.fold_right (fun dig num -> num +. (char_to_float dig) /. 10.0) digits 0.0)))
    (fun ((int_part, _), float_part) -> (float_of_int int_part) +. float_part);;

(* char parser *)

let special_chars = list_to_string ['\''; '\\'; '\"'];;

let char_nt =
  (PC.with_errormsg (PC.wrap
    (PC.char '\'')
    (PC.disj_list [
      PC.diff 
        (PC.range (char_of_int 0) (char_of_int 128)) 
        (PC.one_of special_chars);
      PC.packaten 
        (PC.char '\\')
        (PC.one_of special_chars)
        (fun (_, ch) -> ch)
    ])
    (PC.char '\'')) "Failed while parsing a char literal");;

(* string parser *)

let string_nt =
  (PC.with_errormsg (PC.pack
    (PC.wrap
      (PC.char '"')
      (PC.star (PC.disj_list [
        PC.diff 
          (PC.range (char_of_int 0) (char_of_int 128))
          (PC.one_of special_chars);
        PC.packaten 
          (PC.char '\\')
          (PC.one_of special_chars)
          (fun (_, ch) -> ch)
      ]))
      (PC.char '"'))
    list_to_string) "Failed while parsing a string literal");;

(* Var *)
let var_nt = 
  (PC.packaten
    (PC.range_ci 'A' 'Z')
    (PC.star (PC.disj_list [PC.range_ci 'A' 'Z'; PC.one_of "_*=?!@#$<>"; PC.range '0' '9']))
    (fun (first, rest) -> String.concat "" [String.make 1 first; list_to_string rest]));;

(* type annotation parser *)

type type_expr =
  | TInt
  | TFloat
  | TChar
  | TDouble
  | TVoid
  | Unkn of string
  | TPointer of type_expr
  | TArr of type_expr * int
  | TFunc of type_expr * type_expr list
  | TStruct of (string * type_expr) list;;

type part_type =
  | PTPointer
  | PTFunc of type_expr list;;

let type_keywords = [
  ("int", TInt);
  ("float", TFloat);
  ("char", TChar);
  ("double", TDouble);
  ("void", TVoid)
];;

(* 
<base-type> -> int | double | float | char | void
<function-type> -> <type> <name><lparen><param>*<rparen>
<type> -> <type> <name><lparen><param>*<rparen> | <type><star> | <base-type>
<type> -> <base-type><type'>
<type'> -> <name><lparen><param>*<rparen><type'> | <star><type'> | \epsilon
 *)

let base_type_nt =
  (PC.disj
    (PC.pack var_nt (fun v -> Unkn v))
    (PC.disj_list (List.map 
      (fun (typestr, typetype) -> 
        (PC.pack (PC.word typestr) (fun _ -> typetype)))
      type_keywords)));;

(* let rec pointer_type_nt s =
  (PC.packaten
    base_type_nt
    (PC.plus (PC.wrapws (PC.char '*')))
    (fun (t, stars) -> List.fold_left (fun t _ -> TPointer t) t stars)) s *)

let rec part_types_to_type (bt, pts) =
  match pts with
    | PTPointer :: pts -> TPointer (part_types_to_type (bt, pts))
    | (PTFunc params) :: [] -> TFunc (bt, params)
    | [] -> bt
    | _ -> raise (ParserError "error while parsing types") ;;

let rec func_type_nt s =
  (PC.packaten
    (PC.paren (PC.wrapws (PC.caten
      (PC.char '*')
      (PC.maybe var_nt))))
    (PC.paren 
      (PC.separated type_nt (PC.wrapws (PC.char ','))))
    (fun (_, params_t) -> PTFunc params_t)) s

and type_nt s = 
  (PC.with_errormsg
  (PC.wrapws 
    (PC.packaten
      base_type_nt
      (PC.wrapws type'_nt)
      part_types_to_type))
   "Failed to parse type") s

and type'_nt s =
  (PC.disj_list [
    (PC.packaten
      func_type_nt
      type'_nt
      (fun (ft, ts) -> ft :: ts));
    (PC.packaten
      (PC.wrapws (PC.char '*'))
      type'_nt
      (fun (_, ts) -> PTPointer :: ts));
    (PC.pack PC.nt_epsilon (fun _ -> []))
  ]) s;;

(***** Expressions *****)

type expression =
  | Const of const
  | Var of string
  | FuncCall of expression * expression list
  | PreUnaryExpression of string * expression
  | PostUnrayExpression of expression * string
  | BinaryExpresion of string * expression * expression
  | TernaryExpression of expression * expression * expression
  | Accessor of expression * string
  | PAccessor of expression * string
  | Index of expression * expression;;

let const_nt =
  PC.pack
    (PC.disj_list [
      (PC.pack float_nt (fun f -> Flt f));
      (PC.pack int_nt (fun n -> Int n));
      (PC.pack char_nt (fun c -> Chr c));
      (PC.pack string_nt (fun s -> Str s));
    ])
    (fun c -> Const c);;

(* 

<expr> -> <ternary>
<ternary> -> <binary> (? <expr> : <expr>)*
<binary> -> <binary-pred-0>
<binary-pred-0> -> <binary-pred-1> (<binary-pred-0-op> <binary-pred-1>)*
...
<binary-pred-n> -> <left-unary> (<binary-pred-n-op> <left-unary>)*
<left-unary> -> (<left-unary-op>)*<right-unary>
<right-unary> -> <base>(<right-unary-op>)*
<base> -> <var> | <const>

*)
(* A list of lists of operators
 * each list contains operators with the same precedance
 * the lists are ordered by precedance where the first list has the least precedance *)

let base_expr_nt =
  PC.disj
    (PC.pack var_nt (fun v -> Var v))
    const_nt;;

let rec right_unary_nt s = 
  (PC.packaten
    base_expr_nt
    (PC.star (PC.disj_list [
      PC.pack (PC.disj_list [PC.word "++"; PC.word "--";]) (fun op e -> PostUnrayExpression(e, list_to_string op));
      PC.pack (PC.paren (PC.separated expression_nt (PC.char ','))) (fun args e -> FuncCall (e, args));
      PC.pack (PC.sqrparen expression_nt) (fun index e -> Index (e, index));
      PC.packaten (PC.char '.') var_nt (fun (_, v) e ->  Accessor (e, v));
      PC.packaten (PC.word "->") var_nt (fun (_, v) e -> PAccessor (e, v));
    ]))
    (fun (base, ops) -> List.fold_left (fun e pre_exp -> pre_exp e) base ops)) s

and left_unary_nt s =
  let left_unary_ops = ["++"; "--"; "!"; "~"; "+"; "-"; "*"; "&"] in
  (PC.packaten
    (PC.star (PC.disj_list (List.map PC.word left_unary_ops)))
    right_unary_nt
    (fun (ops, e) -> List.fold_right (fun op e -> PreUnaryExpression (list_to_string op, e)) ops e)) s

and binary_expr_nt s =
  (List.fold_left (fun parser pre_parser -> pre_parser parser) left_unary_nt
  (List.map 
    (fun ops parser -> 
      (PC.packaten
        parser
        (PC.star
          (PC.caten
            (PC.disj_list (List.map (fun op -> PC.wrapws (PC.word op)) ops))
            parser))
        (fun (e, es) -> 
          List.fold_left
            (fun e1 (op, e2) -> BinaryExpresion (list_to_string op, e1, e2))
            e
            es)))
  [
    ["*"; "/"; "%"];
    ["+"; "-"];
    ["<<"; ">>"];
    ["<="; ">="; "<"; ">"];
    ["=="; "!="];
    ["&"];
    ["^"];
    ["|"];
    ["&&"];
    ["||"];
  ])) s

and expression_nt s = (PC.wrapws binary_expr_nt) s;;

(****** Statements ******)

type statement =
  | IfStatement of expression * statement list * statement list option
  | ForStatement of (statement * statement * statement) * statement list
  | FuncDecStatement of type_expr * string * (type_expr * string) list * statement list option
  | VariableDec of type_expr * (string * expression option) list
  | Assignment of expression * expression
  | ExprStatement of expression
  | ReturnStatement of expression
  | TypedefStatement of type_expr * string
  | StructDec of string option * statement list;;

(* Typedef *)
let typedef_nt = 
  PC.with_errormsg (PC.packaten4
    (PC.word "typedef")
    (PC.with_errormsg (PC.wrapws type_nt) "expected type")
    (PC.with_errormsg (PC.wrapws var_nt) "expected new type name")
    (PC.char ';')
    (fun (_, t, name, _) -> TypedefStatement (t, name)))
  "Failed to parse typedef";;

(* Variable Declaration *)

let vardec_nt =
  PC.with_errormsg 
  (PC.packaten3
    type_nt
    (PC.separatedplus
      (PC.caten
        (PC.wrapws var_nt)
        (PC.maybe (PC.packaten
          (PC.wrapws (PC.char '='))
          expression_nt
          (fun (_, value) -> value))))
      (PC.char ','))
    (PC.char ';')
    (fun (vars_type, vars_and_vals, _) -> VariableDec (vars_type, vars_and_vals)))
  "Failed to parse variable declaration";;

(* Assignment *)
let assignemnt_nt =
  PC.with_errormsg
  (PC.packaten4
    expression_nt
    (PC.wrapws (PC.char '='))
    expression_nt
    (PC.char ';')
    (fun (lhs, _, rhs, _) -> Assignment (lhs, rhs)))
  "Failed to parse assignment";;

(* Return *)

let return_nt =
  PC.with_errormsg
  (PC.packaten3
    (PC.word "return")
    expression_nt
    (PC.char ';')
    (fun (_, e, _) -> ReturnStatement e))
  "Failed to parse return statement";;

let rec sequence_nt s = 
  (PC.pack 
    (PC.caten PC.lcurparen (PC.starcaten statement_nt PC.rcurparen))
    (fun (_, (stmts, _)) -> stmts)) s

(* if parser *)
and if_nt s =
  (PC.with_errormsg
  (PC.packaten4
    (PC.wrapws (PC.word "if"))
    (PC.wrapws (PC.paren expression_nt))
    (PC.with_errormsg sequence_nt "Failed to parse if body")
    (PC.maybe (PC.packaten
      (PC.wrapws (PC.word "else"))
      sequence_nt
      (fun (_, stmts) -> stmts)))
    (fun (_, pred, stmts, else_stmts) -> IfStatement (pred, stmts, else_stmts)))
   "Failed to parse if statement") s

(* for parser *)
and for_nt s = 
  (PC.with_errormsg
  (PC.packaten3
    (PC.wrapws (PC.word "for"))
    (PC.wrapws (PC.paren
        (PC.caten3 statement_nt statement_nt expression_nt (* TODO: change to a statement without a ; *))))
    sequence_nt
    (fun (_, (init, pred, next), body) -> ForStatement ((init, pred, ExprStatement next), body)))
   "Failed to parse for statement") s

and stmtexpr_nt s = 
  (PC.packaten 
    expression_nt
    (PC.char ';')
    (fun (e, _) -> ExprStatement e)) s

(* function parser *)

and func_dec_nt s = 
  (PC.packaten4
    type_nt
    var_nt
    (PC.paren 
      (PC.separated 
        (PC.caten type_nt var_nt)
        (PC.wrapws (PC.char ','))))
    (PC.disj
      (PC.pack (PC.char ';') (fun _ -> None))
      (PC.pack sequence_nt (fun s -> Some(s))))
    (fun (t, name, params, body) -> FuncDecStatement (t, name, params, body))) s

and structdec_nt s =
  (PC.packaten4
    (PC.word "struct")
    (PC.maybe (PC.wrapws var_nt))
    sequence_nt
    (PC.char ';')
    (fun (_, name, members, _) -> StructDec (name, members))) s

and statement_nt s = (PC.wrapws (PC.disj_list [
  typedef_nt;
  structdec_nt;
  return_nt;
  for_nt;
  if_nt;
  func_dec_nt;
  vardec_nt;
  assignemnt_nt;
  stmtexpr_nt;
]) s);;

(* exception X_no_match2 of string;; *)

let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;

let rec info_to_string is_first = function
  | PC.NoMatchInfo ((row, col), None, _) -> 
      if is_first 
        then Printf.sprintf "Error at row: %d col: %d\n" row col 
        else "\n"
  | PC.NoMatchInfo ((row, col), Some msg, None) -> 
      if is_first
        then Printf.sprintf "Error at row: %d col: %d. %s\n" row col msg
        else Printf.sprintf "%s\n" msg
  | PC.NoMatchInfo ((row, col), Some msg, Some info) -> 
      if is_first
        then Printf.sprintf "Error at row: %d col: %d. %s: %s" row col msg (info_to_string false info)
        else Printf.sprintf "%s: %s" msg (info_to_string false info);;

  let program_nt s = 
  try (PC.starcaten statement_nt PC.nt_end_of_input) ((string_to_list s), (0, 0))
  with PC.X_no_match info -> (Printf.printf "%s" (info_to_string true info); raise (PC.X_no_match info));;
  (* | (stmts, []) -> stmts
  | (stmts, rem) -> (raise (X_no_match2 (list_to_string rem)));; *)