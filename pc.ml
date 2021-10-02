(* pc.ml
 * A parsing-combinators package for ocaml
 *
 * Prorammer: Mayer Goldberg, 2018
 *)

(* general list-processing procedures *)

let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;

let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;	  

let lowercase_ascii  =
  let delta = int_of_char 'A' - int_of_char 'a' in
  fun ch ->
  if ('A' <= ch && ch <= 'Z')
  then char_of_int ((int_of_char ch) - delta)
  else ch;;

let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

let list_to_string s =
  String.concat "" (List.map (fun ch -> String.make 1 ch) s);;

module PC = struct

(* the parsing combinators defined here *)
  
exception X_not_yet_implemented;;

type no_match_info = 
  NoMatchInfo of (int * int) * string option * no_match_info option;;

exception X_no_match of no_match_info;;

let next_loc e loc = 
  let (row, col) = loc in
  if e = '\n' then (row + 1, 0) else (row, col + 1);;

type parser_inp = char list * (int * int);;

let const pred ((s, loc): parser_inp) =
  match s with
  | [] -> raise (X_no_match (NoMatchInfo (loc, None, None)))
  | e :: s ->
     if (pred e) then (e, (s, (next_loc e loc)))
     else raise (X_no_match (NoMatchInfo (loc, None, None)));;

let with_errormsg nt msg s =
  try (nt s)
  with X_no_match ((NoMatchInfo (loc, msg2, infos)) as info) ->
    match msg2 with
      | None -> raise (X_no_match (NoMatchInfo (loc, Some msg, infos)))
      | Some(msg2) -> raise (X_no_match (NoMatchInfo (loc, Some msg, Some info)));;

let caten nt1 nt2 s =
  let (e1, s) = (nt1 s) in
  let (e2, s) = (nt2 s) in
  ((e1, e2), s);;

let caten3 nt1 nt2 nt3 s =
  let (e1, s) = (nt1 s) in
  let (e2, s) = (nt2 s) in
  let (e3, s) = (nt3 s) in
  ((e1, e2, e3), s);;

let caten4 nt1 nt2 nt3 nt4 s =
  let (e1, s) = (nt1 s) in
  let (e2, s) = (nt2 s) in
  let (e3, s) = (nt3 s) in
  let (e4, s) = (nt4 s) in
  ((e1, e2, e3, e4), s);;

let caten5 nt1 nt2 nt3 nt4 nt5 s =
    let (e1, s) = (nt1 s) in
    let (e2, s) = (nt2 s) in
    let (e3, s) = (nt3 s) in
    let (e4, s) = (nt4 s) in
    let (e5, s) = (nt5 s) in
    ((e1, e2, e3, e4, e5), s);;

let pack nt f s =
  let (e, s) = (nt s) in
  ((f e), s);;

let packaten nt1 nt2 f s = pack (caten nt1 nt2) f s;;
let packaten3 nt1 nt2 nt3 f s = pack (caten3 nt1 nt2 nt3) f s;;
let packaten4 nt1 nt2 nt3 nt4 f s = pack (caten4 nt1 nt2 nt3 nt4) f s;;
let packaten5 nt1 nt2 nt3 nt4 nt5 f s = pack (caten5 nt1 nt2 nt3 nt4 nt5) f s;;

let wrap left nt right =
  packaten3 left nt right
    (fun (_, e, _) -> e);;

let nt_epsilon s = ([], s);;

let caten_list nts =
  List.fold_right
    (fun nt1 nt2 ->
     pack (caten nt1 nt2)
	  (fun (e, es) -> (e :: es)))
    nts
    nt_epsilon;;

let max_loc ((NoMatchInfo ((row1, col1), msg1, rest1)) as info1)
            ((NoMatchInfo ((row2, col2), msg2, rest2)) as info2) = 
  if row1 > row2 then info1
  else if row1 = row2 then (if col1 > col2 then info1 else info2)
  else info2;;

let disj nt1 nt2 s =
    try (nt1 s) with (X_no_match info1) -> 
    try (nt2 s) with (X_no_match info2) -> 
      raise (X_no_match (max_loc info1 info2));;

let nt_none (_, loc) = raise (X_no_match (NoMatchInfo (loc, None, None)));;
  
let disj_list nts = List.fold_right disj nts nt_none;;

let delayed thunk s =
  thunk() s;;

let nt_end_of_input (s, loc) = match s with
  | []  -> ([], ([], loc))
  | _ -> raise (X_no_match (NoMatchInfo (loc, None, None)));;

let rec star nt s =
  try let (e, s) = (nt s) in
      let (es, s) = (star nt s) in
      (e :: es, s)
  with (X_no_match _) -> ([], s);;

let rec starcaten nt1 nt2 s = 
  try let (e, s) = (nt1 s) in
      let ((es, last), s) = (starcaten nt1 nt2 s) in
      ((e :: es, last), s)
  with (X_no_match info1) ->
    try let (e, s) = (nt2 s) in (([], e), s)
    with (X_no_match info2) -> raise (X_no_match (max_loc info1 info2))

let plus nt =
  packaten nt (star nt) (fun (e, es) -> (e :: es));;

let guard nt pred (s, loc) =
  let ((e, _) as result) = (nt (s, loc)) in
  if (pred e) then result
  else raise (X_no_match (NoMatchInfo (loc, None, None)));;
  
let diff nt1 nt2 (s, loc) =
  let to_match = 
    let result = nt1 (s, loc) in
    try let _ = nt2 (s, loc) in None
    with (X_no_match _) -> Some(result) in
  match to_match with
  | None -> raise (X_no_match (NoMatchInfo (loc, None, None)))
  | Some(result) -> result;;

let not_followed_by nt1 nt2 (s, loc) =
  let to_match =
    let ((_, s) as result) = nt1 (s, loc) in
	  try let _ = (nt2 s) in None
	  with (X_no_match _) -> (Some(result)) in
  match to_match with
  | None -> raise (X_no_match (NoMatchInfo (loc, None, None)))
  | Some(result) -> result;;
	  
let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with (X_no_match _) -> (None, s);;

(* useful general parsers for working with text *)

let make_char equal ch1 = 
  with_errormsg (const (fun ch2 -> equal ch1 ch2)) (Printf.sprintf "expected a %c" ch1);;

let char = make_char (fun ch1 ch2 -> ch1 = ch2);;

let char_ci =
  make_char (fun ch1 ch2 ->
	     (lowercase_ascii ch1) =
	       (lowercase_ascii ch2));;

let make_word char str = 
  List.fold_right
    (fun nt1 nt2 -> pack (caten nt1 nt2) (fun (a, b) -> a :: b))
    (List.map char (string_to_list str))
    nt_epsilon;;

let word = make_word char;;

let word_ci = make_word char_ci;;

let make_one_of char str =
  List.fold_right
    disj
    (List.map char (string_to_list str))
    nt_none;;

let one_of = make_one_of char;;

let one_of_ci = make_one_of char_ci;;

let nt_whitespace = const (fun ch -> ch <= ' ');;

let comment_nt = 
  let nt = 
    (star (disj
      (not_followed_by (char '*') (char '/'))
      (const (fun c -> c != '*')))) in
  wrap (word "/*") nt (word "*/");;

let line_comment_nt =
  caten (word "//") (star (const (fun c -> c != '\n')))

let whitespaces_nt = 
  let packer = fun _ -> ' ' in
  (star (disj_list [
    (pack (one_of " \n\t\r") packer);
    (pack comment_nt packer);
    (pack line_comment_nt packer)
  ]));;

let wrapws nt = wrap whitespaces_nt nt whitespaces_nt;;

let lparen = char '(';;

let rparen = char ')';;

let paren nt = wrap lparen nt rparen;;

let lcurparen = char '{';;

let rcurparen = char '}';;

let curparen nt = wrap lcurparen nt rcurparen;;

let lsqrparen = char '[';;

let rsqrparen = char ']';;

let sqrparen nt = wrap lsqrparen nt rsqrparen;;

let separated nt sep =
  disj
    (packaten 
      nt
      (star (packaten sep nt (fun (_, e) -> e)))
      (fun (e, es) -> e :: es))
    nt_epsilon;;

let separatedplus nt sep =
  (packaten
    nt
    (star (packaten sep nt (fun (_, e) -> e)))
    (fun (e, es) -> e :: es));;

let make_range leq ch1 ch2 =
  const (fun ch -> (leq ch1 ch) && (leq ch ch2));;

let range = make_range (fun ch1 ch2 -> ch1 <= ch2);;

let range_ci =
  make_range (fun ch1 ch2 ->
	      (lowercase_ascii ch1) <=
		(lowercase_ascii ch2));;

let nt_any = const (fun ch -> true);;

let trace_pc desc nt s =
  try let ((e, s') as args) = (nt s)
      in
      (Printf.printf ";;; %s matched the head of \"%s\", and the remaining string is \"%s\"\n"
		     desc
		     (list_to_string s)
		     (list_to_string s') ;
       args)
  with (X_no_match (NoMatchInfo ((row, col), reason, infos))) as e ->
    (Printf.printf ";;; %s failed on \"%s\" at row: %d col: %d. reason: %s\n"
		   desc
		   (list_to_string s)
       row col
       "" ;
     raise e);;

(* testing the parsers *)

let test_string nt str =
  let (e, s) = (nt (string_to_list str)) in
  (e, (Printf.sprintf "->[%s]" (list_to_string s)));;

end;; (* end of struct PC *)

(* end-of-input *)
