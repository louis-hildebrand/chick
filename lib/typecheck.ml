open Syntax
module Context = Map.Make (String)
module Syntax = Syntax

type context = tp Context.t

exception Type_error of string

exception
  Unsupported of string (* for unsupported constructs, not type errors *)

exception Not_implemented of string

let string_of_context (ctx : context) : string =
  Context.fold (fun k v acc -> acc ^ k ^ " : " ^ string_of_tp v ^ ", ") ctx "["
  ^ "]"

let counter = ref 0 (* Counter for fresh variables *)

(** Create a fresh variable. *)
let get_fresh_var () : string =
  let v = !counter in
  counter := !counter + 1;
  "#" ^ string_of_int v

let%test _ = get_fresh_var () = "#0"

(** Check whether the types [t1] and [t2] are equal. *)
let rec type_eq (t1 : tp) (t2 : tp) : bool =
  match (t1, t2) with
  | Nat, Nat -> true
  | Vec t1', Vec t2' -> check_term_eq t1' t2' (* check if lengths are equal *)
  | Pi (x, tpA, tpB), Pi (y, tpC, tpD) ->
      (* Change the vars x and y into a fresh unseen variable just for the sake of the comparison *)
      let fresh_var = sv (get_fresh_var ()) in
      let tpA = type_subst tpA x fresh_var in
      let tpB = type_subst tpB x fresh_var in
      let tpC = type_subst tpC y fresh_var in
      let tpD = type_subst tpD y fresh_var in
      type_eq tpA tpC && type_eq tpB tpD
  | _, _ -> false

(** Perform [t/x]T on the type [T]. *)
and type_subst (typ : tp) (x : string) (t : chk_tm) : tp =
  match typ with
  | Nat -> Nat
  | Vec len -> Vec (check_term_subst len x t)
  | Pi (y, _, _) when x == y -> typ
  | Pi (y, tpA, tpB) ->
      (* Change the var y into a fresh unseen variable to avoid the case where y \in FV(t) *)
      let fresh_var = get_fresh_var () in
      let tpA = type_subst tpA y (sv fresh_var) in
      let tpB = type_subst tpB y (sv fresh_var) in
      Pi (fresh_var, type_subst tpA x t, type_subst tpB x t)

(** Check whether the checkable terms [t1] and [t2] are equal. *)
and check_term_eq (t1 : chk_tm) (t2 : chk_tm) : bool =
  match (t1, t2) with
  | Num n1, Num n2 -> n1 = n2
  | Sum t1', Sum t2' -> sum_eq t1' t2'
  | Nil, Nil -> true
  | Syn s1, Syn s2 -> syn_term_eq s1 s2
  | _, _ -> raise (Unsupported "[check_term_eq]")

(** Check whether the checkable sum terms [sum1] and [sum2] are equal. *)
and sum_eq (sum1 : chk_tm list) (sum2 : chk_tm list) : bool =
  (* Flatten sum term (e.g. 2 + (3 + (x+5)) + 4 = 2 + 3 + x + 5 + 4) *)
  let rec flatten_sum (s : chk_tm list) : chk_tm list =
    List.fold_right
      (fun t acc ->
        match t with Sum s' -> flatten_sum s' @ acc | _ -> t :: acc)
      [] s
  in
  (* Partially evaluate and sort a sum term (e.g. 2 + 3 + y + 5 + 4 + x = 14 + x + y) *)
  let sort_and_partially_eval_sum (s : chk_tm list) : chk_tm list =
    let sum =
      List.fold_left
        (fun acc t -> match t with Num n -> acc + n | _ -> acc)
        0 s
    in
    let vars =
      List.filter (fun t -> match t with Syn (Var _) -> true | _ -> false) s
    in
    let others =
      List.filter
        (fun t ->
          match t with Num _ -> false | Syn (Var _) -> false | _ -> true)
        s
    in
    let sorted_vars =
      List.sort
        (fun t1 t2 ->
          match (t1, t2) with
          | Syn (Var v1), Syn (Var v2) -> String.compare v1 v2
          | _ -> 0 (* keep order unchanged *))
        vars
    in
    (Num sum :: sorted_vars) @ others
  in
  let sum1 = sort_and_partially_eval_sum (flatten_sum sum1) in
  let sum2 = sort_and_partially_eval_sum (flatten_sum sum2) in
  if List.length sum1 <> List.length sum2 then false
  else List.for_all2 (fun t1 t2 -> check_term_eq t1 t2) sum1 sum2

(** Check whether the synthesizable terms [s1] and [s2] are equal. *)
and syn_term_eq (s1 : syn_tm) (s2 : syn_tm) : bool =
  match (s1, s2) with
  | Var x1, Var x2 -> x1 = x2
  | _ -> raise (Unsupported "[syn_term_eq]")

(** Perform [e/x]t on the checkable term [t]. *)
and check_term_subst (t : chk_tm) (x : string) (e : chk_tm) : chk_tm =
  match t with
  | Lam (y, _) when x == y -> t
  | Lam (y, body) ->
      let fresh_var = get_fresh_var () in
      let body = check_term_subst body y (sv fresh_var) in
      Lam (fresh_var, check_term_subst body x e)
  | Fix (y, _) when x == y -> t
  | Fix (y, body) ->
      let fresh_var = get_fresh_var () in
      let body = check_term_subst body y (sv fresh_var) in
      Fix (fresh_var, check_term_subst body x e)
  | Num _ -> t
  | Sum sum -> Sum (List.map (fun t' -> check_term_subst t' x e) sum)
  | Nil -> Nil
  | Cons (len, head, tail) ->
      Cons
        ( check_term_subst len x e,
          check_term_subst head x e,
          check_term_subst tail x e )
  | Syn s -> (
      match s with Var y when x == y -> e | _ -> Syn (syn_term_subst s x e))
  | VecMatch (vec, nil_case, len_name, head_name, tail_name, cons_case) ->
      VecMatch
        ( syn_term_subst vec x e,
          check_term_subst nil_case x e,
          len_name,
          head_name,
          tail_name,
          check_term_subst cons_case x e )
  | NatMatch (nat, zero_case, pred_name, non_zero_case) ->
      NatMatch
        ( syn_term_subst nat x e,
          check_term_subst zero_case x e,
          pred_name,
          check_term_subst non_zero_case x e )

(** Perform [e/x]s on the synthesizable term [s]. *)
and syn_term_subst (s : syn_tm) (x : string) (e : chk_tm) : syn_tm =
  match s with
  | Var y when x <> y -> s
  | App (s1, t1) -> App (syn_term_subst s1 x e, check_term_subst t1 x e)
  | Head (len, vec) -> Head (check_term_subst len x e, syn_term_subst vec x e)
  | Tail (len, vec) -> Tail (check_term_subst len x e, syn_term_subst vec x e)
  | _ -> raise (Unsupported "[syn_term_subst] Not yet supported term for syn.")

(* unit tests for check_term_subst and syn_term_subst *)
let%test _ = check_term_subst (Lam ("x", Num 42)) "x" (Num 0) = Lam ("x", Num 42)

let%test _ =
  check_term_subst (Lam ("y", Num 42)) "x" (Num 0) = Lam ("#1", Num 42)

let%test _ = check_term_subst (Lam ("y", sv "x")) "x" (Num 0) = Lam ("#2", Num 0)
let%test _ = check_term_subst (Lam ("y", sv "x")) "y" (Num 0) = Lam ("y", sv "x")
let%test _ = check_term_subst (Fix ("x", Num 42)) "x" (Num 0) = Fix ("x", Num 42)

let%test _ =
  check_term_subst (Fix ("y", Num 42)) "x" (Num 0) = Fix ("#3", Num 42)

let%test _ = check_term_subst (Fix ("y", sv "x")) "x" (Num 0) = Fix ("#4", Num 0)
let%test _ = check_term_subst (Fix ("y", sv "x")) "y" (Num 0) = Fix ("y", sv "x")

let%test _ =
  check_term_subst (Sum [ Num 0; Num 1; sv "x"; sv "y" ]) "x" (Num 2)
  = Sum [ Num 0; Num 1; Num 2; sv "y" ]

let%test _ =
  check_term_subst (Sum [ Num 0; Num 1; sv "x"; sv "y" ]) "x" (sv "y")
  = Sum [ Num 0; Num 1; sv "y"; sv "y" ]

let%test _ =
  check_term_subst (Cons (Num 0, Num 1, Nil)) "x" (Num 0)
  = Cons (Num 0, Num 1, Nil)

let%test _ =
  check_term_subst (Cons (Num 0, sv "x", Nil)) "x" (Num 0)
  = Cons (Num 0, Num 0, Nil)

let%test _ = check_term_subst (sv "x") "x" (Num 42) = Num 42
let%test _ = check_term_subst (sv "x") "y" (Num 42) = sv "x"

(* unit tests for sum_eq *)
let%test _ =
  sum_eq
    [ Num 3; Num 9; sv "y"; sv "x"; Num 1; Num 2; sv "z" ]
    [ Num 15; sv "x"; sv "y"; sv "z" ]

(* unit tests for check_term_eq and syn_term_eq *)
let%test _ = check_term_eq (Num 0) (Num 0)
let%test _ = check_term_eq (Num 1) (Num 1)
let%test _ = not (check_term_eq (Num 1) (Num 2))

let%test _ =
  check_term_eq
    (Sum [ Num 3; Num 9; sv "y"; sv "x"; Num 1; Num 2; sv "z" ])
    (Sum [ Num 15; sv "x"; sv "y"; sv "z" ])

let%test _ = check_term_eq (sv "x") (sv "x")
let%test _ = not (check_term_eq (sv "x") (sv "y"))

(* unit tests for type_subst *)
let%test _ = type_subst (Vec (Num 0)) "x" (Num 0) = Vec (Num 0)
let%test _ = type_subst (Vec (sv "x")) "x" (Num 0) = Vec (Num 0)
let%test _ = type_subst (Pi ("x", Nat, Nat)) "x" (Num 0) = Pi ("x", Nat, Nat)

let%test _ =
  type_subst (Pi ("x", Nat, Vec (sv "x"))) "x" (Num 0)
  = Pi ("x", Nat, Vec (sv "x"))

let%test _ =
  type_subst (Pi ("x", Nat, Vec (sv "n"))) "n" (Num 45)
  = Pi ("#5", Nat, Vec (Num 45))

let%test _ =
  type_subst (Pi ("x", Nat, Pi ("_", Vec (sv "x"), Vec (sv "n")))) "n" (Num 15)
  = Pi ("#6", Nat, Pi ("#8", Vec (sv "#6"), Vec (Num 15)))

(* unit tests for type_eq *)
let%test _ = type_eq (Vec (Num 0)) (Vec (Num 0))
let%test _ = type_eq (Vec (Num 1)) (Vec (Num 1))
let%test _ = type_eq (Vec (sv "y")) (Vec (sv "y"))
let%test _ = not (type_eq (Vec (sv "x")) (Vec (sv "y")))
let%test _ = not (type_eq (Vec (Num 1)) (Vec (Num 0)))

let%test _ =
  type_eq
    (Vec (Sum [ Num 3; Num 9; sv "y"; sv "x"; Num 1; Num 2; sv "z" ]))
    (Vec (Sum [ Num 15; sv "x"; sv "y"; sv "z" ]))

let%test _ = type_eq (Pi ("x", Nat, Nat)) (Pi ("y", Nat, Nat))

let%test _ =
  type_eq
    (Pi ("x", Nat, Pi ("y", Nat, Vec (sv "x"))))
    (Pi ("x", Nat, Pi ("y", Nat, Vec (sv "x"))))

let%test _ =
  type_eq
    (Pi ("a", Nat, Pi ("b", Nat, Vec (sv "a"))))
    (Pi ("b", Nat, Pi ("a", Nat, Vec (sv "b"))))

let%test _ = not (type_eq (Pi ("x", Nat, Nat)) (Pi ("y", Nat, Vec (Num 0))))

(** Check that, in context [ctx], [tm] has type [typ]. *)
let rec check (ctx : context) (tm : chk_tm) (typ : tp) : unit =
  match (tm, typ) with
  | Lam (x, body), Pi (_, tpA, tpB) -> check (ctx |> Context.add x tpA) body tpB
  | Fix (x, body), typ -> check (ctx |> Context.add x typ) body typ
  | Num _, Nat -> ()
  | Sum xs, Nat -> List.iter (fun t -> check ctx t Nat) xs
  | Syn s, typ when type_eq (syn ctx s) typ -> ()
  | Nil, typ ->
      if type_eq typ (Vec (Num 0)) then () else raise (Type_error "nil")
  | Cons (len, head, tail), Vec l ->
      check ctx len Nat;
      check ctx head Nat;
      check ctx tail (Vec len);
      if check_term_eq l (Sum [ len; Num 1 ]) then ()
      else raise (Type_error "cons term does not produce the expected type")
  | NatMatch (Var v, zero_case, pred_name, succ_case), typ
    when syn ctx (Var v) = Nat ->
      check ctx
        (check_term_subst zero_case v (Num 0))
        (type_subst typ v (Num 0));
      let succ = Sum [ sv pred_name; Num 1 ] in
      check
        (ctx |> Context.add pred_name Nat)
        (check_term_subst succ_case v succ)
        (type_subst typ v succ)
  | VecMatch (vec, nil_case, len_name, head_name, tail_name, cons_case), typ
    -> (
      let vec_type = syn ctx vec in
      match vec_type with
      | Vec (Syn (Var v)) ->
          check ctx
            (check_term_subst nil_case v (Num 0))
            (type_subst typ v (Num 0));
          let ctx =
            ctx |> Context.add len_name Nat |> Context.add head_name Nat
            |> Context.add tail_name (Vec (sv len_name))
          in
          let cons = Sum [ sv len_name; Num 1 ] in
          check ctx (check_term_subst cons_case v cons) (type_subst typ v cons)
      | _ -> raise (Type_error "vmatch type error"))
  | tm, typ ->
      raise
        (Type_error
           ("Term '" ^ string_of_chk_tm tm
          ^ "' does not have the expected type '" ^ string_of_tp typ
          ^ "' with context '" ^ string_of_context ctx ^ "'"))

(** Synthesize a type from the term [t] in context [ctx]. *)
and syn (ctx : context) (t : syn_tm) : tp =
  match t with
  | Var x -> (
      match Context.find_opt x ctx with
      | Some typ -> typ
      | None -> raise (Type_error ("Free variable: " ^ x)))
  | App (s, t) -> (
      let s_type = syn ctx s in
      match s_type with
      | Pi (x, tpA, tpB) ->
          check ctx t tpA;
          type_subst tpB x t
      | _ -> raise (Type_error "applying non-function"))
  | Head (len, vec) -> (
      let in_type = Vec (Sum [ sv "x"; Num 1 ]) in
      let out_type = Nat in
      let f_type = Pi ("x", Nat, arrow in_type out_type) in
      let f_app = apps (Var "#head") [ len; Syn vec ] in
      let head_type = syn (ctx |> Context.add "#head" f_type) f_app in
      match head_type with
      | Nat -> Nat
      | _ -> raise (Type_error "head of vector does not return type Nat"))
  | Tail (len, vec) -> (
      let in_type = Vec (Sum [ sv "x"; Num 1 ]) in
      let out_type = Vec (sv "x") in
      let f_type = Pi ("x", Nat, arrow in_type out_type) in
      let f_app = apps (Var "#tail") [ len; Syn vec ] in
      let tail_type = syn (ctx |> Context.add "#tail" f_type) f_app in
      match tail_type with
      | Vec (Syn (Var "x")) -> Vec (Syn (Var "x"))
      | _ -> raise (Type_error "tail of vector does not return type Vec[x]"))

(* unit tests for syn and check *)
let count_down =
  Fix
    ( "count_down",
      Lam
        ( "n",
          NatMatch
            ( Var "n",
              Nil,
              "m",
              Cons (sv "m", sv "m", Syn (App (Var "count_down", sv "m"))) ) ) )

let%test _ =
  let ctx = Context.empty in
  check ctx count_down (Pi ("n", Nat, Vec (Syn (Var "n")))) = ()

let count_up_from =
  Fix
    ( "cnt",
      Lam
        ( "n",
          Lam
            ( "z",
              NatMatch
                ( Var "n",
                  Nil,
                  "n'",
                  Cons
                    ( sv "n'",
                      sv "z",
                      Syn (apps (Var "cnt") [ sv "n'"; Sum [ sv "z"; Num 1 ] ])
                    ) ) ) ) )

let%test _ =
  let ctx = Context.empty in
  check ctx count_up_from (Pi ("n", Nat, arrow Nat (Vec (sv "n")))) = ()

let map =
  Fix
    ( "map",
      Lam
        ( "n",
          Lam
            ( "v",
              Lam
                ( "f",
                  VecMatch
                    ( Var "v",
                      Nil,
                      "m",
                      "x",
                      "xs",
                      Cons
                        ( sv "m",
                          Syn (App (Var "f", sv "x")),
                          Syn (apps (Var "map") [ sv "m"; sv "f"; sv "xs" ]) )
                    ) ) ) ) )

let%test _ =
  check Context.empty map
    (Pi ("n", Nat, arrows [ Vec (sv "n"); arrow Nat Nat; Vec (sv "n") ]))
  = ()

(** Typecheck a complete program. *)
let check_program (prog : program) : unit =
  let rec f (ctx : context) (decls : program) : unit =
    match decls with
    | [] -> ()
    | d :: ds ->
        check ctx d.body d.typ;
        f (ctx |> Context.add d.name d.typ) ds
  in
  f Context.empty prog
