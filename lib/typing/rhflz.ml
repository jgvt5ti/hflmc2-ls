open Hflmc2_util
open Hflmc2_syntax
open Id
open Rtype

type t =
  | Bool   of bool
  | Var    of Rtype.t Id.t
  (* template is used for tracking counterexample. *)
  | Or     of t * t * template * template
  | And    of t * t * template * template
  | Abs    of Rtype.t Id.t * t
  | App    of t * t * template
  | Forall of Rtype.t Id.t * t * template
  (* constructers only for hflz *)
  | Arith  of Arith.t
  | LsArith of Arith.lt
  | Pred   of Formula.pred * Arith.t list
  | LsPred of Formula.ls_pred * Arith.t list * Arith.lt list

let rec print_formula = function
  | Bool x when x -> Printf.printf "tt"
  | Bool _ -> Printf.printf "ff"
  | Var x -> Printf.printf "%s" (Id.to_string x)
  | Or (x, y, _, _) -> 
    Printf.printf "(";
    print_formula x;
    Printf.printf " || ";
    print_formula y;
    Printf.printf ")";
  | And (x, y, tx, ty) -> 
    Printf.printf "(";
    print_formula x;
    print_string ":";
    print_template tx;
    Printf.printf " && ";
    print_formula y;
    print_string ":";
    print_template ty;
    Printf.printf ")";
  | Abs (x, y) -> 
    Printf.printf "(";
    Printf.printf "\\";
    print_rtype x.ty;
    Printf.printf ".";
    print_formula y;
    Printf.printf ")"
  | Forall (x, y, _) -> 
    Printf.printf "(";
    Printf.printf "∀";
    print_rtype x.ty;
    Printf.printf ".";
    print_formula y;
    Printf.printf ")"
  | App (x, y, _) -> 
    Printf.printf "(";
    print_formula x;
    Printf.printf " ";
    print_formula y;
    Printf.printf ")";
  | Arith x ->
    Print.arith Fmt.stdout x;
    Fmt.flush Fmt.stdout () 
  | LsArith x ->
    Print.ls_arith Fmt.stdout x;
    Fmt.flush Fmt.stdout () 
  | Pred (x,[f1; f2]) -> 
    Print.arith Fmt.stdout f1;
    Print.pred Fmt.stdout x;
    Print.arith Fmt.stdout f2;
    Fmt.flush Fmt.stdout () ;
  | LsPred (x, [], [f1; f2]) -> 
    Print.ls_arith Fmt.stdout f1;
    Print.ls_pred Fmt.stdout x;
    Print.ls_arith Fmt.stdout f2;
    Fmt.flush Fmt.stdout () ;
  | Pred (x,_) -> 
    Print.pred Fmt.stdout x;
    Fmt.flush Fmt.stdout ()
  | LsPred (x,_, _) -> 
    Print.ls_pred Fmt.stdout x;
    Fmt.flush Fmt.stdout () 

let rec is_simple p = match p with
  | And(x, y, _, _) | Or(x, y, _, _) -> (is_simple x && is_simple y)
  | Arith(_) | LsArith(_)| Var(_) | App(_) | Abs(_) | Forall(_) -> false
  | _ -> true

exception TriedToNegateApp
let rec negate p = match p with
  | Arith(_) | LsArith(_) | Var(_) | App(_) | Abs(_) | Forall(_) -> raise TriedToNegateApp
  | Or(x, y, t1, t2) -> And(negate x, negate y, t1, t2)
  | And(x, y, t1, t2) -> Or(negate x, negate y, t1, t2)
  | Bool x -> Bool (not x)
  | Pred(p, l) -> Pred(Formula.negate_pred p, l)
  | LsPred(p, a, l) -> LsPred(Formula.negate_ls_pred p, a, l)
let rec translate_if hflz = match hflz with
  | Or(And(a, b, s1, s2), And(a', b', s1',s2'), t1, t2) ->
    let fa = is_simple a in
    let fa' = is_simple a' in
    let fb = is_simple b in
    let fb' = is_simple b' in
    if fa && fa' && negate a = a' then
      And(Or(a', translate_if b, s1, s2), Or(a, translate_if b', s1', s2'), t1, t2)
    else if fa && fb' && negate a = b' then
      And(Or(b', translate_if b, s1, s2), Or(a, translate_if a', s1', s2'), t1, t2)
    else if fb && fa' && negate b = a' then
      And(Or(a', translate_if a, s1, s2), Or(b, translate_if b', s1', s2'), t1, t2)
   else if fb && fb' && negate b = b' then
      And(Or(b', translate_if a, s1, s2), Or(b, translate_if a', s1', s2'), t1, t2)
    else 
      Or(And(translate_if a, translate_if b, s1, s2), And(translate_if a', translate_if b', s1', s2'), t1, t2)
  | Or(x, y, t1, t2) -> Or(translate_if x, translate_if y, t1, t2)
  | And(x, y, t1, t2) -> And(translate_if x, translate_if y, t1, t2)
  | Abs (x, t) -> Abs(x, translate_if t)
  | x -> x

type hes_rule =
  { var  : Rtype.t Id.t
  ; body : t
  ; fix  : Fixpoint.t
  }

let lookup_rule f hes =
  List.find_exn hes ~f:(fun r -> Id.eq r.var f)

let rec replace_rule f rule hes = match hes with
  | [] -> failwith "Not found"
  | rule'::xs when Id.eq rule'.var rule.var
    -> rule::xs
  | rule'::xs -> rule'::replace_rule f rule xs

type hes = hes_rule list

let rec bottom_hflz = function
  | Rtype.RBool _ -> Bool(false)
  | Rtype.RArrow(x, y) -> 
    Abs(Id.gen x, bottom_hflz y)
  | Rtype.RInt(RId(x)) -> Var({x with ty=Rtype.(RInt(RId(x)))})
  | Rtype.RList(RLId(x)) -> Var({x with ty=Rtype.(RList(RLId(x)))})
  | Rtype.RInt(RArith(x)) -> Arith(x)
  | Rtype.RList(RLsArith(x)) -> LsArith(x)

let rec top_hflz = function
  | Rtype.RBool _ -> Bool(true)
  | Rtype.RArrow(x, y) -> 
    Abs(Id.gen x, top_hflz y)
  | Rtype.RInt(RId(x)) -> Var({x with ty=Rtype.(RInt(RId(x)))})
  | Rtype.RInt(RArith(x)) -> Arith(x)
  | Rtype.RList(RLId(x)) -> Var({x with ty=Rtype.(RList(RLId(x)))})
  | Rtype.RList(RLsArith(x)) -> LsArith(x)