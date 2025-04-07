open Context
open Solver
open Syntax

type context = tp Context.t

exception Type_error of string

(** Create a fresh variable. *)
let get_fresh_var : unit -> string =
  let counter = ref 0 in
  let get () =
    let v = !counter in
    counter := !counter + 1;
    "#" ^ string_of_int v
  in
  get

let%test _ = get_fresh_var () = "#0"
let%test _ = get_fresh_var () = "#1"

(** Check if a sum is a valid size for a vector *)
let rec is_valid_size (t : chk_tm) : bool =
  match t with
  | Num n -> n >= 0
  | Sum ts -> List.for_all is_valid_size ts
  | Syn (Var _) -> true
  | _ -> false

let%test _ = is_valid_size (Num 0)
let%test _ = is_valid_size (sv "x")
let%test _ = is_valid_size (Sum [ Num 0; Num 1; sv "x"; sv "y"; Num 2; Num 3 ])
let%test _ = not (is_valid_size (Sum [ Num 0; Num (-1); sv "x" ]))

(** Check whether 2 sizes are equal. *)
let same_size (t1 : chk_tm) (t2 : chk_tm) (delta : equation list) : bool =
  match (len_of_tm t1, len_of_tm t2) with
  | Some n1, Some n2 -> Solver.always_equal (mk_equation (n1, n2)) delta
  | _ -> raise (Type_error "Invalid size for vector.")

(* unit tests for same_size *)

let%test _ = same_size (Num 0) (Num 0) []
let%test _ = same_size (Num 1) (Num 1) []
let%test _ = not (same_size (Num 1) (Num 2) [])
let%test _ = same_size (Num 0) (Sum [ Num 0; Num 0 ]) []
let%test _ = same_size (Sum [ Num 0; Num 0 ]) (Sum [ Num 0; Num 0 ]) []
let%test _ = same_size (Sum [ Num 0; Num 1 ]) (Sum [ Num 0; Num 0; Num 1 ]) []
let%test _ = same_size (sv "x") (sv "x") []
let%test _ = not (same_size (sv "x") (sv "y") [])
let%test _ = same_size (sv "x") (sv "y") [ mk_equation (LVar "x", LVar "y") ]

let%test _ =
  same_size (sv "x") (sv "y")
    [ mk_equation (LSum [ LVar "x"; LNum 1 ], LSum [ LVar "y"; LNum 1 ]) ]

let%test _ = same_size (Sum [ sv "x"; Num 0 ]) (Sum [ Num 0; sv "x" ]) []
let%test _ = same_size (Sum [ Num 0; sv "x" ]) (Sum [ sv "x"; Num 0 ]) []
let%test _ = same_size (Sum [ Num 0; sv "x" ]) (Sum [ Num 0; Num 0; sv "x" ]) []

let%test _ =
  same_size (Sum [ sv "y"; sv "x" ]) (Sum [ Num 0; sv "y"; sv "x" ]) []

let%test _ = same_size (Sum [ sv "y"; sv "x" ]) (Sum [ sv "x"; sv "y" ]) []
let%test _ = not (same_size (Sum [ sv "y"; sv "x" ]) (Sum [ Num 0; sv "x" ]) [])

let%test _ =
  same_size
    (Sum [ Num 3; Num 9; sv "y"; sv "x"; Num 1; Num 2; sv "z" ])
    (Sum [ Num 15; sv "x"; sv "y"; sv "z" ])
    []

(** Perform [e/x]t on the checkable term [t]. *)
let rec chk_tm_subst (t : chk_tm) (x : string) (e : chk_tm) : chk_tm =
  match t with
  | Lam (y, _) when x == y -> t
  | Lam (y, body) ->
      let fresh_var = get_fresh_var () in
      let body = chk_tm_subst body y (sv fresh_var) in
      Lam (fresh_var, chk_tm_subst body x e)
  | Fix (y, _) when x == y -> t
  | Fix (y, body) ->
      let fresh_var = get_fresh_var () in
      let body = chk_tm_subst body y (sv fresh_var) in
      Fix (fresh_var, chk_tm_subst body x e)
  | Num _ -> t
  | Sum sum -> Sum (List.map (fun t' -> chk_tm_subst t' x e) sum)
  | Nil -> Nil
  | Cons (len, head, tail) ->
      Cons (chk_tm_subst len x e, chk_tm_subst head x e, chk_tm_subst tail x e)
  | Syn s -> syn_tm_subst s x e
  | VecMatch (vec, nil_case, _, _, _, cons_case) -> (
      let fresh_len_name = get_fresh_var () in
      let fresh_head_name = get_fresh_var () in
      let fresh_tail_name = get_fresh_var () in
      let cons_case = chk_tm_subst cons_case x (sv fresh_len_name) in
      let cons_case = chk_tm_subst cons_case x (sv fresh_head_name) in
      let cons_case = chk_tm_subst cons_case x (sv fresh_tail_name) in
      let vec_sub = syn_tm_subst vec x e in
      match vec_sub with
      | Syn s ->
          VecMatch
            ( s,
              chk_tm_subst nil_case x e,
              fresh_len_name,
              fresh_head_name,
              fresh_tail_name,
              chk_tm_subst cons_case x e )
      | _ -> failwith "TODO")
  | NatMatch (nat, zero_case, _, non_zero_case) -> (
      let fresh_pred_name = get_fresh_var () in
      let non_zero_case = chk_tm_subst non_zero_case x (sv fresh_pred_name) in
      let nat_sub = syn_tm_subst nat x e in
      match nat_sub with
      | Syn s ->
          NatMatch
            ( s,
              chk_tm_subst zero_case x e,
              fresh_pred_name,
              chk_tm_subst non_zero_case x e )
      | _ -> failwith "TODO")
  | Unreachable -> Unreachable

(** Perform [e/x]s on the synthesizable term [s]. *)
and syn_tm_subst (s : syn_tm) (x : string) (e : chk_tm) : chk_tm =
  match s with
  | Var y when x <> y -> Syn s
  | Var y when x == y -> e
  | App (s1, t1) -> (
      let s1' = syn_tm_subst s1 x e in
      let t1' = chk_tm_subst t1 x e in
      match s1' with
      | Syn s' -> Syn (App (s', t1'))
      | Lam (y, body) ->
          let fresh_var = get_fresh_var () in
          let body = chk_tm_subst body y (sv fresh_var) in
          (* Beta reduction / hereditary substitution *)
          chk_tm_subst body y t1'
      | _ -> failwith "TODO")
  | _ -> failwith "TODO"

(* unit tests for chk_tm_subst and syn_tm_subst *)
let%test _ = chk_tm_subst (Lam ("x", Num 42)) "x" (Num 0) = Lam ("x", Num 42)
let%test _ = chk_tm_subst (Lam ("y", Num 42)) "x" (Num 0) = Lam ("#2", Num 42)
let%test _ = chk_tm_subst (Lam ("y", sv "x")) "x" (Num 0) = Lam ("#3", Num 0)
let%test _ = chk_tm_subst (Lam ("y", sv "x")) "y" (Num 0) = Lam ("y", sv "x")
let%test _ = chk_tm_subst (Fix ("x", Num 42)) "x" (Num 0) = Fix ("x", Num 42)
let%test _ = chk_tm_subst (Fix ("y", Num 42)) "x" (Num 0) = Fix ("#4", Num 42)
let%test _ = chk_tm_subst (Fix ("y", sv "x")) "x" (Num 0) = Fix ("#5", Num 0)
let%test _ = chk_tm_subst (Fix ("y", sv "x")) "y" (Num 0) = Fix ("y", sv "x")

let%test _ =
  chk_tm_subst (Sum [ Num 0; Num 1; sv "x"; sv "y" ]) "x" (Num 2)
  = Sum [ Num 0; Num 1; Num 2; sv "y" ]

let%test _ =
  chk_tm_subst (Sum [ Num 0; Num 1; sv "x"; sv "y" ]) "x" (sv "y")
  = Sum [ Num 0; Num 1; sv "y"; sv "y" ]

let%test _ =
  chk_tm_subst (Cons (Num 0, Num 1, Nil)) "x" (Num 0) = Cons (Num 0, Num 1, Nil)

let%test _ =
  chk_tm_subst (Cons (Num 0, sv "x", Nil)) "x" (Num 0) = Cons (Num 0, Num 0, Nil)

let%test _ = chk_tm_subst (sv "x") "x" (Num 42) = Num 42
let%test _ = chk_tm_subst (sv "x") "y" (Num 42) = sv "x"

(** Perform [t/x]T on the type [T]. *)
let rec tp_subst (typ : tp) (x : string) (t : chk_tm) : tp =
  match typ with
  | Nat -> Nat
  | Vec len -> Vec (chk_tm_subst len x t)
  | Pi (y, _, _) when x == y -> typ
  | Pi (y, tpA, tpB) ->
      (* Change the var y into a fresh unseen variable to avoid the case where y \in FV(t) *)
      let fresh_var = get_fresh_var () in
      let tpA = tp_subst tpA y (sv fresh_var) in
      let tpB = tp_subst tpB y (sv fresh_var) in
      Pi (fresh_var, tp_subst tpA x t, tp_subst tpB x t)

(* unit tests for tp_subst *)
let%test _ = tp_subst (Vec (Num 0)) "x" (Num 0) = Vec (Num 0)
let%test _ = tp_subst (Vec (sv "x")) "x" (Num 0) = Vec (Num 0)
let%test _ = tp_subst (Pi ("x", Nat, Nat)) "x" (Num 0) = Pi ("x", Nat, Nat)

let%test _ =
  tp_subst (Pi ("x", Nat, Vec (sv "x"))) "x" (Num 0)
  = Pi ("x", Nat, Vec (sv "x"))

let%test _ =
  tp_subst (Pi ("x", Nat, Vec (sv "n"))) "n" (Num 45)
  = Pi ("#6", Nat, Vec (Num 45))

let%test _ =
  tp_subst (Pi ("x", Nat, Pi ("_", Vec (sv "x"), Vec (sv "n")))) "n" (Num 15)
  = Pi ("#7", Nat, Pi ("#9", Vec (sv "#7"), Vec (Num 15)))

(** Check whether the types [t1] and [t2] are equal. *)
let rec tp_eq (t1 : tp) (t2 : tp) (delta : equation list) : bool =
  match (t1, t2) with
  | Nat, Nat -> true
  | Vec t1', Vec t2' -> same_size t1' t2' delta
  | Pi (x, tpA, tpB), Pi (y, tpC, tpD) ->
      (* Change the vars x and y into a fresh unseen variable just for the sake of the comparison *)
      let fresh_var = sv (get_fresh_var ()) in
      let tpA = tp_subst tpA x fresh_var in
      let tpB = tp_subst tpB x fresh_var in
      let tpC = tp_subst tpC y fresh_var in
      let tpD = tp_subst tpD y fresh_var in
      tp_eq tpA tpC delta && tp_eq tpB tpD delta
  | _, _ -> false

(* unit tests for tp_eq *)
let%test _ = tp_eq (Vec (Num 0)) (Vec (Num 0)) []
let%test _ = tp_eq (Vec (Num 1)) (Vec (Num 1)) []
let%test _ = tp_eq (Vec (sv "y")) (Vec (sv "y")) []
let%test _ = not (tp_eq (Vec (sv "x")) (Vec (sv "y")) [])
let%test _ = not (tp_eq (Vec (Num 1)) (Vec (Num 0)) [])

let%test _ =
  tp_eq
    (Vec (Sum [ Num 3; Num 9; sv "y"; sv "x"; Num 1; Num 2; sv "z" ]))
    (Vec (Sum [ Num 15; sv "x"; sv "y"; sv "z" ]))
    []

let%test _ = tp_eq (Pi ("x", Nat, Nat)) (Pi ("y", Nat, Nat)) []

let%test _ =
  tp_eq
    (Pi ("x", Nat, Pi ("y", Nat, Vec (sv "x"))))
    (Pi ("x", Nat, Pi ("y", Nat, Vec (sv "x"))))
    []

let%test _ =
  tp_eq
    (Pi ("a", Nat, Pi ("b", Nat, Vec (sv "a"))))
    (Pi ("b", Nat, Pi ("a", Nat, Vec (sv "b"))))
    []

let%test _ = not (tp_eq (Pi ("x", Nat, Nat)) (Pi ("y", Nat, Vec (Num 0))) [])

let%test _ =
  tp_eq (Vec (sv "x")) (Vec (sv "y")) [ mk_equation (LVar "x", LVar "y") ]

let%test _ =
  tp_eq
    (Vec (sv "x"))
    (Vec (sv "y"))
    [ mk_equation (LSum [ LVar "x"; LNum 1 ], LSum [ LVar "y"; LNum 1 ]) ]

(** Substitute in a context. *)
let ctx_subst (ctx : context) (x : string) (t : chk_tm) : context =
  (* TODO: Apparently subst in a context is prone to subtle bugs. Delete it ASAP. *)
  (* For example, what happens if the variable being substituted appears in the context? *)
  Context.mapi (fun _ typ -> tp_subst typ x t) ctx

(* unit tests for ctx_subst *)
let%test _ =
  let ctx = Context.of_seq (List.to_seq [ ("n", Nat); ("v", Vec (sv "n")) ]) in
  let expected =
    Context.of_seq (List.to_seq [ ("n", Nat); ("v", Vec (Num 0)) ])
  in
  let actual = ctx_subst ctx "n" (Num 0) in
  actual = expected

(** Check that, in context [ctx], [tm] has type [typ]. *)
let rec check (gamma : context) (delta : equation list) (tm : chk_tm) (typ : tp)
    : unit =
  match (tm, typ) with
  | Lam (x, body), Pi (_, tpA, tpB) ->
      check (gamma |> Context.add x tpA) delta body tpB
  | Fix (x, body), typ -> check (gamma |> Context.add x typ) delta body typ
  | Num _, Nat -> ()
  | Sum xs, Nat -> List.iter (fun t -> check gamma delta t Nat) xs
  | Syn s, typ when tp_eq (synth gamma delta s) typ delta -> ()
  | Nil, typ when tp_eq typ (Vec (Num 0)) delta -> ()
  | Cons (len, head, tail), Vec n when same_size n (Sum [ len; Num 1 ]) delta ->
      check gamma delta len Nat;
      check gamma delta head Nat;
      check gamma delta tail (Vec len)
  | NatMatch (s, zero_case, pred_name, succ_case), typ
    when synth gamma delta s = Nat -> (
      match len_of_tm (Syn s) with
      | Some n ->
          let check_zero_case () =
            let is_reachable =
              Solver.can_equal (mk_equation (n, LNum 0)) delta
            in
            match (zero_case, is_reachable) with
            | Unreachable, false -> ()
            | Unreachable, true ->
                (* TODO: Give an example instantiation? *)
                raise
                  (Type_error
                     "The zero branch is reachable but not implemented.")
            | t, true ->
                let delta' = mk_equation (n, LNum 0) :: delta in
                check gamma delta' t typ
            | _, false ->
                raise
                  (Type_error
                     "The zero branch is unreachable and should therefore be \
                      left unimplemented.")
          in
          let check_succ_case () =
            let succ = LSum [ LVar pred_name; LNum 1 ] in
            let is_reachable = Solver.can_equal (mk_equation (n, succ)) delta in
            match (succ_case, is_reachable) with
            | Unreachable, false -> ()
            | Unreachable, true ->
                raise
                  (Type_error
                     "The succ branch is reachable but not implemented.")
            | t, true ->
                let gamma' = gamma |> Context.add pred_name Nat in
                let delta' = mk_equation (n, succ) :: delta in
                check gamma' delta' t typ
            | _, false ->
                raise
                  (Type_error
                     "The succ branch is unreachable and should therefore be \
                      left unimplemented.")
          in
          check_zero_case ();
          check_succ_case ()
      | _ ->
          raise
            (Type_error
               ("Target of nmatch is " ^ string_of_syn_tm s
              ^ ", which is unsupported. It must be a length.")))
  | VecMatch (vec, nil_case, len_name, head_name, tail_name, cons_case), typ
    -> (
      let vec_type = synth gamma delta vec in
      match vec_type with
      | Vec t -> (
          match len_of_tm t with
          | Some n ->
              let check_nil_case () =
                let is_reachable =
                  Solver.can_equal (mk_equation (n, LNum 0)) delta
                in
                match (nil_case, is_reachable) with
                | Unreachable, false -> ()
                | Unreachable, true ->
                    raise
                      (Type_error
                         "The nil branch is reachable but not implemented.")
                | t, true ->
                    let delta' = mk_equation (n, LNum 0) :: delta in
                    check gamma delta' t typ
                | _, false ->
                    raise
                      (Type_error
                         "The nil branch is unreachable and should therefore \
                          be left unimplemented.")
              in
              let check_cons_case () =
                let succ = LSum [ LVar len_name; LNum 1 ] in
                let is_reachable =
                  Solver.can_equal (mk_equation (n, succ)) delta
                in
                match (cons_case, is_reachable) with
                | Unreachable, false -> ()
                | Unreachable, true ->
                    raise
                      (Type_error
                         "The cons branch is reachable but not implemented.")
                | t, true ->
                    let gamma' =
                      gamma |> Context.add len_name Nat
                      |> Context.add head_name Nat
                      |> Context.add tail_name (Vec (sv len_name))
                    in
                    let delta' = mk_equation (n, succ) :: delta in
                    check gamma' delta' t typ
                | _, false ->
                    raise
                      (Type_error
                         "The cons branch is unreachable and should therefore \
                          be left unimplemented.")
              in
              check_nil_case ();
              check_cons_case ()
          | None ->
              raise
                (Type_error
                   ("Vec type " ^ string_of_tp vec_type
                  ^ " is not valid. It must be a length.")))
      | t ->
          raise
            (Type_error
               ("Target of vmatch synthesized type " ^ string_of_tp t
              ^ ". It must be a vector.")))
  | Unreachable, _ ->
      raise
        (Type_error
           ("'"
           ^ string_of_chk_tm Unreachable
           ^ "' can only be used directly inside a match."))
  | tm, typ ->
      raise
        (Type_error
           ("Term '" ^ string_of_chk_tm tm
          ^ "' does not have the expected type '" ^ string_of_tp typ ^ "'."))

(** Synthesize a type from the term [t] in context [ctx]. *)
and synth (gamma : context) (delta : equation list) (t : syn_tm) : tp =
  let res_tp =
    match t with
    | Var x -> (
        match Context.find_opt x gamma with
        | Some typ -> typ
        | None -> raise (Type_error ("Free variable: " ^ x)))
    | App (s, t) -> (
        let s_type = synth gamma delta s in
        match s_type with
        | Pi (x, tpA, tpB) ->
            check gamma delta t tpA;
            tp_subst tpB x t
        | _ -> raise (Type_error "applying non-function"))
  in
  res_tp

(** Typecheck a complete program. *)
let check_program (prog : program) : unit =
  let rec f (gamma : context) (decls : program) : unit =
    match decls with
    | [] -> ()
    | d :: ds ->
        check gamma [] d.body d.typ;
        f (gamma |> Context.add d.name d.typ) ds
  in
  f Context.empty prog
