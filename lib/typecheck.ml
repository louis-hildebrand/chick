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
  | Bool -> Bool
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
  | Sigma (y, _, _) when x = y -> typ
  | Sigma (y, t1, t2) ->
      (* Rename to avoid variable capture. *)
      let y' = get_fresh_var () in
      let t1' = tp_subst (tp_subst t1 y (sv y')) x t in
      let t2' = tp_subst (tp_subst t2 y (sv y')) x t in
      Sigma (y', t1', t2')

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

let _ = reset_fresh_var_ctr ()
let%test _ = tp_subst (Sigma ("x", Nat, Nat)) "x" (Num 0) = Sigma ("x", Nat, Nat)

let%test _ =
  tp_subst (Sigma ("x", Nat, Vec (LVar "x"))) "x" (Num 0)
  = Sigma ("x", Nat, Vec (LVar "x"))

let%test _ =
  tp_subst (Sigma ("x", Nat, Vec (LVar "n"))) "n" (Num 45)
  = Sigma ("#0", Nat, Vec (LNum 45))

let%test _ =
  let actual =
    tp_subst
      (Sigma ("x", Nat, Sigma ("_", Vec (LVar "x"), Vec (LVar "n"))))
      "n" (Num 15)
  in
  let expected =
    Sigma ("#1", Nat, Sigma ("#3", Vec (LVar "#1"), Vec (LNum 15)))
  in
  actual = expected

(** Perform [[x'/x] n] on the length [n]. *)
let rec len_rename (x' : string) (x : string) (n : len) : len =
  match n with
  | LNum k -> LNum k
  | LVar y when y = x -> LVar x'
  | LVar y -> LVar y
  | LSum terms -> LSum (terms |> List.map (len_rename x' x))

(** Perform [[x'/x] t] on the checkable term [t]. *)
let rec chk_tm_rename (x' : string) (x : string) (t : chk_tm) : chk_tm =
  match t with
  | Lam (y, _) when y = x -> t
  | Lam (y, t) ->
      (* Rename to avoid variable capture. *)
      let y' = get_fresh_var () in
      let t' = chk_tm_rename x' x (chk_tm_rename y' y t) in
      Lam (y', t')
  | Fix (y, _) when y = x -> t
  | Fix (y, t) ->
      (* Rename to avoid variable capture. *)
      let y' = get_fresh_var () in
      let t' = chk_tm_rename x' x (chk_tm_rename y' y t) in
      Fix (y', t')
  | Num k -> Num k
  | Sum terms -> Sum (terms |> List.map (chk_tm_rename x' x))
  | Nil -> Nil
  | Cons (n, y, ys) ->
      Cons (len_rename x' x n, chk_tm_rename x' x y, chk_tm_rename x' x ys)
  | False -> False
  | True -> True
  | Pair (t1, t2) -> Pair (chk_tm_rename x' x t1, chk_tm_rename x' x t2)
  | BoolMatch (s, tt, tf) ->
      let s' = syn_tm_rename x' x s in
      let tt' = chk_tm_rename x' x tt in
      let tf' = chk_tm_rename x' x tf in
      BoolMatch (s', tt', tf')
  | NatMatch (s, t0, t1) ->
      let s' = syn_tm_rename x' x s in
      let t0' = Option.map (chk_tm_rename x' x) t0 in
      let t1' =
        Option.map
          (fun (y, t) ->
            if y = x then (y, t)
            else
              (* Rename to avoid variable capture. *)
              let y' = get_fresh_var () in
              let t' = chk_tm_rename x' x (chk_tm_rename y' y t) in
              (y', t'))
          t1
      in
      NatMatch (s', t0', t1')
  | VecMatch (s, t0, t1) ->
      let s' = syn_tm_rename x' x s in
      let t0' = Option.map (chk_tm_rename x' x) t0 in
      let t1' =
        Option.map
          (fun (y1, y2, y3, t) ->
            if List.mem x [ y1; y2; y3 ] then (y1, y2, y3, t)
            else
              (* Rename to avoid variable capture. *)
              let y1' = get_fresh_var () in
              let y2' = get_fresh_var () in
              let y3' = get_fresh_var () in
              let t' =
                chk_tm_rename x' x
                  (chk_tm_rename y3' y3
                     (chk_tm_rename y2' y2 (chk_tm_rename y1' y1 t)))
              in
              (y1', y2', y3', t'))
          t1
      in
      VecMatch (s', t0', t1')
  | PairMatch (s, y1, y2, t) when x = y1 || x = y2 ->
      PairMatch (syn_tm_rename x' x s, y1, y2, t)
  | PairMatch (s, y1, y2, t) ->
      (* Rename to avoid variable capture. *)
      let s' = syn_tm_rename x' x s in
      let y1' = get_fresh_var () in
      let y2' = get_fresh_var () in
      let t' =
        chk_tm_rename x' x (chk_tm_rename y2' y2 (chk_tm_rename y1' y1 t))
      in
      PairMatch (s', y1', y2', t')
  | Syn s -> Syn (syn_tm_rename x' x s)

(** Perform [[x'/x] s] on the synthesizable term [s]. *)
and syn_tm_rename (x' : string) (x : string) (s : syn_tm) : syn_tm =
  match s with
  | Var y when y = x -> Var x'
  | Var y -> Var y
  | App (s, t) -> App (syn_tm_rename x' x s, chk_tm_rename x' x t)

(* unit tests for chk_tm_rename and syn_tm_rename *)
let%test _ =
  let actual =
    syn_tm_rename "g" "f" (apps (Var "f") [ sv "x"; sv "y"; sv "z" ])
  in
  let expected = apps (Var "g") [ sv "x"; sv "y"; sv "z" ] in
  actual = expected

let _ = reset_fresh_var_ctr ()

let%test _ =
  let actual =
    chk_tm_rename "x'" "x" (Lam ("x", Sum [ sv "x"; sv "x'"; sv "y" ]))
  in
  let expected = Lam ("x", Sum [ sv "x"; sv "x'"; sv "y" ]) in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "x'" "x" (Lam ("x'", Sum [ sv "x"; sv "x'"; sv "y" ]))
  in
  let expected = Lam ("#0", Sum [ sv "x'"; sv "#0"; sv "y" ]) in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "x'" "x" (Lam ("y", Sum [ sv "x"; sv "x'"; sv "y" ]))
  in
  let expected = Lam ("#1", Sum [ sv "x'"; sv "x'"; sv "#1" ]) in
  actual = expected

let _ = reset_fresh_var_ctr ()

let%test _ =
  let actual =
    chk_tm_rename "x'" "x" (Fix ("x", Sum [ sv "x"; sv "x'"; sv "y" ]))
  in
  let expected = Fix ("x", Sum [ sv "x"; sv "x'"; sv "y" ]) in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "x'" "x" (Fix ("x'", Sum [ sv "x"; sv "x'"; sv "y" ]))
  in
  let expected = Fix ("#0", Sum [ sv "x'"; sv "#0"; sv "y" ]) in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "x'" "x" (Fix ("y", Sum [ sv "x"; sv "x'"; sv "y" ]))
  in
  let expected = Fix ("#1", Sum [ sv "x'"; sv "x'"; sv "#1" ]) in
  actual = expected

let _ = reset_fresh_var_ctr ()

let%test _ =
  let actual =
    chk_tm_rename "z'" "z"
      (NatMatch
         (Var "z", Some (sv "z"), Some ("z", Sum [ sv "z"; sv "z'"; sv "w" ])))
  in
  let expected =
    NatMatch
      (Var "z'", Some (sv "z'"), Some ("z", Sum [ sv "z"; sv "z'"; sv "w" ]))
  in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "z'" "z"
      (NatMatch (Var "s", None, Some ("z'", Sum [ sv "z"; sv "z'"; sv "w" ])))
  in
  let expected =
    NatMatch (Var "s", None, Some ("#0", Sum [ sv "z'"; sv "#0"; sv "w" ]))
  in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "z'" "z"
      (NatMatch (Var "s", None, Some ("w", Sum [ sv "z"; sv "z'"; sv "w" ])))
  in
  let expected =
    NatMatch (Var "s", None, Some ("#1", Sum [ sv "z'"; sv "z'"; sv "#1" ]))
  in
  actual = expected

let _ = reset_fresh_var_ctr ()

let%test _ =
  let actual =
    chk_tm_rename "new" "y1"
      (VecMatch
         ( Var "y1",
           Some (sv "y1"),
           Some
             ( "y1",
               "y2",
               "y3",
               Syn (apps (Var "f") [ sv "y1"; sv "y2"; sv "y3"; sv "x" ]) ) ))
  in
  let expected =
    VecMatch
      ( Var "new",
        Some (sv "new"),
        Some
          ( "y1",
            "y2",
            "y3",
            Syn (apps (Var "f") [ sv "y1"; sv "y2"; sv "y3"; sv "x" ]) ) )
  in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "new" "y2"
      (VecMatch
         ( Var "y2",
           Some (sv "y2"),
           Some
             ( "y1",
               "y2",
               "y3",
               Syn (apps (Var "f") [ sv "y1"; sv "y2"; sv "y3"; sv "x" ]) ) ))
  in
  let expected =
    VecMatch
      ( Var "new",
        Some (sv "new"),
        Some
          ( "y1",
            "y2",
            "y3",
            Syn (apps (Var "f") [ sv "y1"; sv "y2"; sv "y3"; sv "x" ]) ) )
  in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "new" "y3"
      (VecMatch
         ( Var "y3",
           Some (sv "y3"),
           Some
             ( "y1",
               "y2",
               "y3",
               Syn (apps (Var "f") [ sv "y1"; sv "y2"; sv "y3"; sv "x" ]) ) ))
  in
  let expected =
    VecMatch
      ( Var "new",
        Some (sv "new"),
        Some
          ( "y1",
            "y2",
            "y3",
            Syn (apps (Var "f") [ sv "y1"; sv "y2"; sv "y3"; sv "x" ]) ) )
  in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "y1" "x"
      (VecMatch
         ( Var "s",
           None,
           Some
             ( "y1",
               "y2",
               "y3",
               Syn (apps (Var "f") [ sv "y1"; sv "y2"; sv "y3"; sv "x" ]) ) ))
  in
  let expected =
    VecMatch
      ( Var "s",
        None,
        Some
          ( "#0",
            "#1",
            "#2",
            Syn (apps (Var "f") [ sv "#0"; sv "#1"; sv "#2"; sv "y1" ]) ) )
  in
  actual = expected

let _ = reset_fresh_var_ctr ()

let%test _ =
  let actual =
    chk_tm_rename "x'" "x"
      (Pair (Sum [ sv "x"; sv "x'"; sv "y" ], Sum [ sv "x'"; sv "z"; sv "x" ]))
  in
  let expected =
    Pair (Sum [ sv "x'"; sv "x'"; sv "y" ], Sum [ sv "x'"; sv "z"; sv "x'" ])
  in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "new" "y1"
      (PairMatch (Var "y1", "y1", "y2", Sum [ sv "y1"; sv "y2"; sv "z" ]))
  in
  let expected =
    PairMatch (Var "new", "y1", "y2", Sum [ sv "y1"; sv "y2"; sv "z" ])
  in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "new" "y2"
      (PairMatch (Var "y2", "y1", "y2", Sum [ sv "y1"; sv "y2"; sv "z" ]))
  in
  let expected =
    PairMatch (Var "new", "y1", "y2", Sum [ sv "y1"; sv "y2"; sv "z" ])
  in
  actual = expected

let%test _ =
  let actual =
    chk_tm_rename "y1" "z"
      (PairMatch (Var "s", "y1", "y2", Sum [ sv "y1"; sv "y2"; sv "z" ]))
  in
  let expected =
    PairMatch (Var "s", "#0", "#1", Sum [ sv "#0"; sv "#1"; sv "y1" ])
  in
  actual = expected

(** Check whether the types [t1] and [t2] are equal. *)
let rec tp_eq (t1 : tp) (t2 : tp) (delta : equation list) : bool =
  match (t1, t2) with
  | Nat, Nat -> true
  | Bool, Bool -> true
  | Vec t1', Vec t2' -> same_size t1' t2' delta
  | Pi (x, tpA, tpB), Pi (y, tpC, tpD) ->
      (* Change the vars x and y into a fresh unseen variable just for the sake of the comparison *)
      let fresh_var = sv (get_fresh_var ()) in
      let tpB = tp_subst tpB x fresh_var in
      let tpD = tp_subst tpD y fresh_var in
      tp_eq tpA tpC delta && tp_eq tpB tpD delta
  | Sigma (x, tpA, tpB), Sigma (y, tpC, tpD) ->
      let z = get_fresh_var () in
      let tpB' = tp_subst tpB x (sv z) in
      let tpD' = tp_subst tpD y (sv z) in
      tp_eq tpA tpC delta && tp_eq tpB' tpD' delta
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

let%test _ = tp_eq Bool Bool []
let%test _ = not (tp_eq Bool Nat [])

let%test _ =
  tp_eq
    (times (times Nat Bool) (times Bool Nat))
    (times (times Nat Bool) (times Bool Nat))
    []

let%test _ = not (tp_eq (times Nat Bool) (times Nat Nat) [])
let%test _ = not (tp_eq (times Bool Nat) (times Nat Nat) [])

let%test _ =
  tp_eq
    (Sigma ("m1", Nat, Vec (LSum [ LVar "m1"; LVar "n" ])))
    (Sigma ("m2", Nat, Vec (LSum [ LVar "n'"; LVar "m2"; LNum 0 ])))
    [ mk_equation (LVar "n", LVar "n'") ]

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
  | False, Bool -> ()
  | True, Bool -> ()
  | Pair (t1, t2), Sigma (x, typ1, typ2) ->
      check gamma delta t1 typ1;
      check gamma delta t2 (tp_subst typ2 x t1)
  | BoolMatch (s, tt, tf), typ when synth gamma delta s = Bool ->
      check gamma delta tt typ;
      check gamma delta tf typ
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
            | Some (y, t), true ->
                (* y may shadow another variable, which can lead to
                   contradictory equations (e.g., n = n + 1, where the n's are
                   actually different)! *)
                let is_shadowing =
                  List.exists
                    (fun n -> StringSet.mem y (vars n))
                    (n :: List.concat [ List.map fst delta; List.map snd delta ])
                in
                let y, t =
                  if is_shadowing then
                    let y' = get_fresh_var () in
                    let t' = chk_tm_rename y' y t in
                    (y', t')
                  else (y, t)
                in
                let gamma' = gamma |> Context.add y Nat in
                let delta' =
                  mk_equation (n, LSum [ LVar y; LNum 1 ]) :: delta
                in
                check gamma' delta' t typ
            | Some (y, t), false ->
                raise
                  (Type_error
                     ("The succ branch (" ^ y ^ " -> " ^ string_of_chk_tm t
                    ^ ") is unreachable and should therefore be left \
                       unimplemented."))
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
            | Some (y1, y2, y3, t), true ->
                (* y1 may shadow an existing variable! *)
                let is_shadowing =
                  List.exists
                    (fun n -> StringSet.mem y1 (vars n))
                    (n :: List.concat [ List.map fst delta; List.map snd delta ])
                in
                let y1, t =
                  if is_shadowing then
                    let y1' = get_fresh_var () in
                    let t' = chk_tm_rename y1' y1 t in
                    (y1', t')
                  else (y1, t)
                in
                let gamma' =
                  gamma |> Context.add y1 Nat |> Context.add y2 Nat
                  |> Context.add y3 (Vec (LVar y1))
                in
                let delta' =
                  mk_equation (n, LSum [ LVar y1; LNum 1 ]) :: delta
                in
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
  | PairMatch (s, x1, x2, t), _ -> (
      match synth gamma delta s with
      | Sigma (x, typ1, typ2) ->
          let gamma' =
            gamma |> Context.add x1 typ1
            |> Context.add x2 (tp_subst typ2 x (sv x1))
          in
          check gamma' delta t typ
      | other ->
          raise
            (Type_error
               ("Subject of pair match synthesized " ^ string_of_tp other
              ^ "'. It must synthesize a Sigma type.")))
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
