open Context
open Solver
open Syntax

type context = tp Context.t

exception Type_error of string

(** Generator for fresh variables. *)
let (get_fresh_var, reset_fresh_var_ctr) : (unit -> string) * (unit -> unit) =
  let counter = ref 0 in
  let get () =
    let v = !counter in
    counter := !counter + 1;
    "#" ^ string_of_int v
  in
  let reset () = counter := 0 in
  (get, reset)

let%test _ = reset_fresh_var_ctr () = ()
let%test _ = get_fresh_var () = "#0"
let%test _ = get_fresh_var () = "#1"
let%test _ = reset_fresh_var_ctr () = ()
let%test _ = get_fresh_var () = "#0"
let%test _ = get_fresh_var () = "#1"

(** Check whether 2 sizes are equal. *)
let same_size (n1 : len) (n2 : len) (delta : equation list) : bool =
  Solver.always_equal (mk_equation (n1, n2)) delta

(* unit tests for same_size *)

let%test _ = same_size (LNum 0) (LNum 0) []
let%test _ = same_size (LNum 1) (LNum 1) []
let%test _ = not (same_size (LNum 1) (LNum 2) [])
let%test _ = same_size (LNum 0) (LSum [ LNum 0; LNum 0 ]) []
let%test _ = same_size (LSum [ LNum 0; LNum 0 ]) (LSum [ LNum 0; LNum 0 ]) []

let%test _ =
  same_size (LSum [ LNum 0; LNum 1 ]) (LSum [ LNum 0; LNum 0; LNum 1 ]) []

let%test _ = same_size (LVar "x") (LVar "x") []
let%test _ = not (same_size (LVar "x") (LVar "y") [])

let%test _ =
  same_size (LVar "x") (LVar "y") [ mk_equation (LVar "x", LVar "y") ]

let%test _ =
  same_size (LVar "x") (LVar "y")
    [ mk_equation (LSum [ LVar "x"; LNum 1 ], LSum [ LVar "y"; LNum 1 ]) ]

let%test _ =
  same_size (LSum [ LVar "x"; LNum 0 ]) (LSum [ LNum 0; LVar "x" ]) []

let%test _ =
  same_size (LSum [ LNum 0; LVar "x" ]) (LSum [ LVar "x"; LNum 0 ]) []

let%test _ =
  same_size (LSum [ LNum 0; LVar "x" ]) (LSum [ LNum 0; LNum 0; LVar "x" ]) []

let%test _ =
  same_size
    (LSum [ LVar "y"; LVar "x" ])
    (LSum [ LNum 0; LVar "y"; LVar "x" ])
    []

let%test _ =
  same_size (LSum [ LVar "y"; LVar "x" ]) (LSum [ LVar "x"; LVar "y" ]) []

let%test _ =
  not (same_size (LSum [ LVar "y"; LVar "x" ]) (LSum [ LNum 0; LVar "x" ]) [])

let%test _ =
  same_size
    (LSum [ LNum 3; LNum 9; LVar "y"; LVar "x"; LNum 1; LNum 2; LVar "z" ])
    (LSum [ LNum 15; LVar "x"; LVar "y"; LVar "z" ])
    []

(** Perform [n'/x]n on the length n. *)
let rec len_subst (n : len) (x : string) (n' : len) : len =
  match n with
  | LNum k -> LNum k
  | LVar y when x = y -> n'
  | LVar y -> LVar y
  | LSum terms -> LSum (List.map (fun n -> len_subst n x n') terms)

(** Perform [t/x]T on the type [T]. *)
let rec tp_subst (typ : tp) (x : string) (t : chk_tm) : tp =
  match typ with
  | Nat -> Nat
  | Vec n -> (
      match len_of_tm t with
      | Some len -> Vec (len_subst n x len)
      | None when not (StringSet.mem x (vars n)) -> Vec n
      | None ->
          raise
            (Type_error
               ("Cannot replace variable '" ^ x ^ "' with non-length term '"
              ^ string_of_chk_tm t ^ "' in '" ^ string_of_tp typ ^ "'.")))
  | Pi (y, _, _) when x = y -> typ
  | Pi (y, tpA, tpB) ->
      (* Change the var y into a fresh unseen variable to avoid the case where y \in FV(t) *)
      let fresh_var = get_fresh_var () in
      let tpA = tp_subst tpA y (sv fresh_var) in
      let tpB = tp_subst tpB y (sv fresh_var) in
      Pi (fresh_var, tp_subst tpA x t, tp_subst tpB x t)

(* unit tests for tp_subst *)
let _ = reset_fresh_var_ctr ()
let%test _ = tp_subst (Vec (LNum 0)) "x" (Num 0) = Vec (LNum 0)
let%test _ = tp_subst (Vec (LVar "x")) "x" (Num 0) = Vec (LNum 0)
let%test _ = tp_subst (Pi ("x", Nat, Nat)) "x" (Num 0) = Pi ("x", Nat, Nat)

let%test _ =
  tp_subst (Pi ("x", Nat, Vec (LVar "x"))) "x" (Num 0)
  = Pi ("x", Nat, Vec (LVar "x"))

let%test _ =
  tp_subst (Pi ("x", Nat, Vec (LVar "n"))) "n" (Num 45)
  = Pi ("#0", Nat, Vec (LNum 45))

let%test _ =
  tp_subst
    (Pi ("x", Nat, Pi ("_", Vec (LVar "x"), Vec (LVar "n"))))
    "n" (Num 15)
  = Pi ("#1", Nat, Pi ("#3", Vec (LVar "#1"), Vec (LNum 15)))

let%test _ =
  let actual = tp_subst (Pi ("_", Vec (LNum 0), Vec (LNum 1))) "x" Nil in
  let expected = Pi ("#4", Vec (LNum 0), Vec (LNum 1)) in
  actual = expected

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
let%test _ = tp_eq (Vec (LNum 0)) (Vec (LNum 0)) []
let%test _ = tp_eq (Vec (LNum 1)) (Vec (LNum 1)) []
let%test _ = tp_eq (Vec (LVar "y")) (Vec (LVar "y")) []
let%test _ = not (tp_eq (Vec (LVar "x")) (Vec (LVar "y")) [])
let%test _ = not (tp_eq (Vec (LNum 1)) (Vec (LNum 0)) [])

let%test _ =
  tp_eq
    (Vec (LSum [ LNum 3; LNum 9; LVar "y"; LVar "x"; LNum 1; LNum 2; LVar "z" ]))
    (Vec (LSum [ LNum 15; LVar "x"; LVar "y"; LVar "z" ]))
    []

let%test _ = tp_eq (Pi ("x", Nat, Nat)) (Pi ("y", Nat, Nat)) []

let%test _ =
  tp_eq
    (Pi ("x", Nat, Pi ("y", Nat, Vec (LVar "x"))))
    (Pi ("x", Nat, Pi ("y", Nat, Vec (LVar "x"))))
    []

let%test _ =
  tp_eq
    (Pi ("a", Nat, Pi ("b", Nat, Vec (LVar "a"))))
    (Pi ("b", Nat, Pi ("a", Nat, Vec (LVar "b"))))
    []

let%test _ = not (tp_eq (Pi ("x", Nat, Nat)) (Pi ("y", Nat, Vec (LNum 0))) [])

let%test _ =
  tp_eq (Vec (LVar "x")) (Vec (LVar "y")) [ mk_equation (LVar "x", LVar "y") ]

let%test _ =
  tp_eq (Vec (LVar "x")) (Vec (LVar "y"))
    [ mk_equation (LSum [ LVar "x"; LNum 1 ], LSum [ LVar "y"; LNum 1 ]) ]

(** Check that, in context [gamma], [n] has type [Nat]. *)
let rec check_len_nat (gamma : context) (n : len) =
  match n with
  | LVar x when Context.find_opt x gamma = Some Nat -> ()
  | LVar x when Context.find_opt x gamma = None ->
      raise (Type_error ("Free variable: " ^ x))
  | LNum k when k >= 0 -> ()
  | LSum terms -> List.iter (fun t -> check_len_nat gamma t) terms
  | _ ->
      raise
        (Type_error
           ("Term '" ^ string_of_len n ^ "' does not have the expected type '"
          ^ string_of_tp Nat ^ "'."))

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
  | Nil, typ when tp_eq typ (Vec (LNum 0)) delta -> ()
  | Cons (len, head, tail), Vec n when same_size n (LSum [ len; LNum 1 ]) delta
    ->
      check_len_nat gamma len;
      check gamma delta head Nat;
      check gamma delta tail (Vec len)
  | NatMatch (s, zero_case, succ_case), typ when synth gamma delta s = Nat -> (
      match len_of_tm (Syn s) with
      | Some n ->
          let check_zero_case () =
            let is_reachable =
              Solver.can_equal (mk_equation (n, LNum 0)) delta
            in
            match (zero_case, is_reachable) with
            | None, false -> ()
            | None, true ->
                (* TODO: Give an example instantiation? *)
                raise
                  (Type_error
                     "The zero branch is reachable but not implemented.")
            | Some t, true ->
                let delta' = mk_equation (n, LNum 0) :: delta in
                check gamma delta' t typ
            | Some _, false ->
                raise
                  (Type_error
                     "The zero branch is unreachable and should therefore be \
                      left unimplemented.")
          in
          let check_succ_case () =
            let is_reachable =
              Solver.can_equal
                (mk_equation (n, LSum [ LVar (get_fresh_var ()); LNum 1 ]))
                delta
            in
            match (succ_case, is_reachable) with
            | None, false -> ()
            | None, true ->
                raise
                  (Type_error
                     "The succ branch is reachable but not implemented.")
            | Some (pred_name, t), true ->
                let succ = LSum [ LVar pred_name; LNum 1 ] in
                let gamma' = gamma |> Context.add pred_name Nat in
                let delta' = mk_equation (n, succ) :: delta in
                check gamma' delta' t typ
            | Some _, false ->
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
  | VecMatch (vec, nil_case, cons_case), typ -> (
      let vec_type = synth gamma delta vec in
      match vec_type with
      | Vec n ->
          let check_nil_case () =
            let is_reachable =
              Solver.can_equal (mk_equation (n, LNum 0)) delta
            in
            match (nil_case, is_reachable) with
            | None, false -> ()
            | None, true ->
                raise
                  (Type_error "The nil branch is reachable but not implemented.")
            | Some t, true ->
                let delta' = mk_equation (n, LNum 0) :: delta in
                check gamma delta' t typ
            | Some _, false ->
                raise
                  (Type_error
                     "The nil branch is unreachable and should therefore be \
                      left unimplemented.")
          in
          let check_cons_case () =
            let is_reachable =
              Solver.can_equal
                (mk_equation (n, LSum [ LVar (get_fresh_var ()); LNum 1 ]))
                delta
            in
            match (cons_case, is_reachable) with
            | None, false -> ()
            | None, true ->
                raise
                  (Type_error
                     "The cons branch is reachable but not implemented.")
            | Some (len_name, head_name, tail_name, t), true ->
                let gamma' =
                  gamma |> Context.add len_name Nat |> Context.add head_name Nat
                  |> Context.add tail_name (Vec (LVar len_name))
                in
                let succ = LSum [ LVar len_name; LNum 1 ] in
                let delta' = mk_equation (n, succ) :: delta in
                check gamma' delta' t typ
            | Some _, false ->
                raise
                  (Type_error
                     "The cons branch is unreachable and should therefore be \
                      left unimplemented.")
          in
          check_nil_case ();
          check_cons_case ()
      | t ->
          raise
            (Type_error
               ("Target of vmatch synthesized type " ^ string_of_tp t
              ^ ". It must be a vector.")))
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
