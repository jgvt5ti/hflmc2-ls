open Eldarica.Dag
open Hflmc2_syntax

type r = [`Invalid | `Unknown]

type value = 
  | VBool of Fpl.t
  | VInt of Arith.t
  | VFun of Rtype.t Id.t * Rhflz.t * env
and env = value IdMap.t

exception Infeasible

let rid_of_arithid id = 
  Id.({name=id.name; id=id.id; ty=Rtype.RInt(RId(id))})

let show_fixpoint = function
  | Fixpoint.Greatest -> "v"
  | Fixpoint.Least -> "u"

let print_rhflz_hes hes =
  List.iter
    (fun {Rhflz.body; var; fix} ->
      print_string @@ Id.to_string var;
      print_string " =";
      print_string @@ show_fixpoint fix;
      print_string " ";
      Rhflz.print_formula body;
      print_string "\n"
    )
    hes

let print_count_map (map : (Rtype.t Id.t * int list) list list) =
  List.map (fun id_args ->
    match id_args with
    | [] -> ""
    | (id, _)::_ ->
      Id.to_string id ^ " -> " ^
        (List.map (fun (_, args) -> "(" ^ (List.map string_of_int args |> String.concat ",") ^ ")") id_args |> String.concat "\n")
  ) map
  |> String.concat "\n"
  
let disprove unsat_proof hes env top = 
  (* no recursive hes *)
  let hes, args_map = Expand.expand unsat_proof hes in
  print_rhflz_hes hes;
  print_endline @@ print_count_map args_map;
  let fml = (Rhflz.lookup_rule top hes).body in
  let eval fml = 
    (* evaluator *)
    let open Rhflz in
    let rec f env fml = match fml with
      | Bool x -> VBool(Fpl.Bool(x))
      | Or(p, q, _, _) -> VBool(Fpl.Or(f_bool env p, f_bool env q))
      | And(p, q, _, _) -> VBool(Fpl.And(f_bool env p, f_bool env q))
      | Pred(a, l, _) -> VBool(Fpl.Pred(a, List.map (f_arith env) l))
      | Arith(a) -> VInt(f_arith env a)
      | Forall(id, e, _) -> 
        begin
        match id.ty with
        | Rtype.RInt(RId(x)) -> 
          VBool(Fpl.Forall ({id with ty = `Int},
            f_bool (IdMap.set env id @@ VInt(Arith.Var(x))) e))
        | Rtype.RInt(RArith(x)) -> 
          VBool(Fpl.Forall ({id with ty = `Int},
            f_bool (IdMap.set env id @@ VInt(x)) e))
        | Rtype.RArrow(_) -> 
          let g = Rhflz.bottom_hflz id.ty in
          begin
          match g with
          | Abs(id, e) -> f (IdMap.set env id @@ VFun(id, e, env)) e
          | _ -> failwith "evaluation error(bottom)"
          end
        | Rtype.RBool(x) -> f (IdMap.set env id @@ VBool(Fpl.Bool(false))) e
        end
      | Var x -> begin match IdMap.find env x with 
        | Some(x) -> x
        | None -> 
        Printf.printf "\nCurrent Environments\n";
        IdMap.iter_keys ~f:(fun key -> 
          Printf.printf "%s\n" @@ Id.to_string key
        ) env;
        Printf.printf "but not found %s\n" @@ Id.to_string x;
         failwith "evaluation error(var not found)"
        end
      | Abs(id, e) -> VFun(id, e, env)
      | App(e1, e2, _) -> 
        let v1 = f env e1 in
        let v2 = f env e2 in
        begin
        match v1 with
        | VFun(id, e, env) -> 
          f (IdMap.set env id v2) e
        | _ -> failwith "runtime error(Disprove.eval)"
        end
    and f_bool env fml = match f env fml with
      | VBool(x) -> x
      | _ -> failwith "runetime error(Disprove f_bool in eval)"
    and f_arith env e = let open Arith in
      match e with 
      | Op(op, l) -> 
        Op(op, List.map (f_arith env) l)
      | Var x -> 
        begin match IdMap.find env x with 
          | Some(VInt(a)) -> a
          | None -> failwith "evaluation error: var not found(f_arith)"
          | _ -> failwith "evaluation error(f_arith)"
        end
      | x -> x
    in 
    f IdMap.empty fml
  in
  let v = eval fml in
  let b = begin
  match v with
  | VBool(v) -> v
  | _ -> failwith "evaluation error"
  end in
  (*
  reduced formula
  print_newline ();
  Fpl.print b;
  print_newline ();
  *)
  match Smt_solver.check_sat_fpl `Z3 b with
  | `Unsat -> `Invalid
  | _ -> `Unknown