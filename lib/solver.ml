open Printf
open Syntax

type equation = len * len

let mk_equation = fun x -> x
let debug = false

type prop =
  | Eq of len * len
  | Geq of len * len
  | Implies of prop * prop
  | And of prop list
  | Forall of string list * prop
  | Exists of string list * prop

let check : prop -> bool =
  let ctx = Z3.mk_context [] in
  let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in
  let rec z3_expr_of_len (vars : string list) (n : len) : Z3.Expr.expr =
    match n with
    | LNum n -> Z3.Arithmetic.Integer.mk_numeral_i ctx n
    | LVar x ->
        (* The library seems to use de Bruijn indices.
           Find de Bruijn level first and then convert to index. *)
        let debruijn_level =
          match List.find_index (fun y -> y = x) vars with
          | Some i -> i
          | None ->
              failwith
                ("BUG: free variable " ^ x
               ^ " while converting length to Z3 expr.")
        in
        let debruijn_idx = List.length vars - 1 - debruijn_level in
        Z3.Quantifier.mk_bound ctx debruijn_idx int_sort
    | LSum ns -> Z3.Arithmetic.mk_add ctx (List.map (z3_expr_of_len vars) ns)
  in
  let rec z3_expr_of_prop (vars : string list) (p : prop) : Z3.Expr.expr =
    match p with
    | Eq (n1, n2) ->
        let lhs = z3_expr_of_len vars n1 in
        let rhs = z3_expr_of_len vars n2 in
        Z3.Boolean.mk_eq ctx lhs rhs
    | Geq (n1, n2) ->
        let lhs = z3_expr_of_len vars n1 in
        let rhs = z3_expr_of_len vars n2 in
        Z3.Arithmetic.mk_ge ctx lhs rhs
    | Implies (p, q) ->
        let p' = z3_expr_of_prop vars p in
        let q' = z3_expr_of_prop vars q in
        Z3.Boolean.mk_implies ctx p' q'
    | And ps -> Z3.Boolean.mk_and ctx (List.map (z3_expr_of_prop vars) ps)
    | Forall (xs, p) ->
        let p' = z3_expr_of_prop (List.concat [ vars; xs ]) p in
        let sorts = List.init (List.length xs) (fun _ -> int_sort) in
        let symbols = List.map (fun x -> Z3.Symbol.mk_string ctx x) xs in
        let quant =
          Z3.Quantifier.mk_forall ctx sorts symbols p' (Some 1) [] [] None None
        in
        Z3.Quantifier.expr_of_quantifier quant
    | Exists (xs, p) ->
        let p' = z3_expr_of_prop (List.concat [ vars; xs ]) p in
        let sorts = List.init (List.length xs) (fun _ -> int_sort) in
        let symbols = List.map (fun x -> Z3.Symbol.mk_string ctx x) xs in
        let quant =
          Z3.Quantifier.mk_exists ctx sorts symbols p' (Some 1) [] [] None None
        in
        Z3.Quantifier.expr_of_quantifier quant
  in
  let solver = Z3.Solver.mk_simple_solver ctx in
  let check (e : Z3.Expr.expr) : bool =
    match Z3.Solver.check solver [ e ] with
    | SATISFIABLE ->
        if debug then printf "SAT: %s\n" (Z3.Expr.to_string e) else ();
        true
    | UNSATISFIABLE | UNKNOWN ->
        if debug then printf "UNSAT: %s\n" (Z3.Expr.to_string e) else ();
        false
  in
  fun p -> check (z3_expr_of_prop [] p)

let eq_vars (eqs : equation list) : str_set =
  List.fold_left
    (fun acc (n1, n2) ->
      StringSet.union acc (StringSet.union (vars n1) (vars n2)))
    StringSet.empty eqs

let always_equal (eq : equation) (assumptions : equation list) : bool =
  let vars = eq_vars (eq :: assumptions) in
  let var_list = List.of_seq (StringSet.to_seq vars) in
  let antecedent =
    (* All variables must be natural numbers (i.e., >= 0). *)
    let nat_prop = And (List.map (fun x -> Geq (LVar x, LNum 0)) var_list) in
    (* All the assumptions must hold. *)
    let assumptions_prop =
      And (List.map (fun (n1, n2) -> Eq (n1, n2)) assumptions)
    in
    And [ nat_prop; assumptions_prop ]
  in
  let p = Forall (var_list, Implies (antecedent, Eq (fst eq, snd eq))) in
  check p

let%test _ = always_equal (LVar "n", LVar "n") []

let%test _ =
  always_equal (LSum [ LVar "m"; LNum 1 ], LSum [ LVar "m"; LNum 1 ]) []

let%test _ =
  always_equal (LVar "n", LVar "n'")
    [ (LSum [ LVar "n"; LNum 1 ], LSum [ LVar "n'"; LNum 1 ]) ]

let%test _ = not (always_equal (LVar "n", LVar "n'") [])
let%test _ = not (always_equal (LNum 0, LNum 1) [])

let can_equal (eq : equation) (assumptions : equation list) : bool =
  let vars = eq_vars (eq :: assumptions) in
  let var_list = List.of_seq (StringSet.to_seq vars) in
  let antecedent =
    (* All variables must be natural numbers (i.e., >= 0). *)
    let nat_prop = And (List.map (fun x -> Geq (LVar x, LNum 0)) var_list) in
    (* All the assumptions must hold. *)
    let assumptions_prop =
      And (List.map (fun (n1, n2) -> Eq (n1, n2)) assumptions)
    in
    And [ nat_prop; assumptions_prop ]
  in
  let p = Exists (var_list, And [ antecedent; Eq (fst eq, snd eq) ]) in
  check p

let%test _ = can_equal (LVar "n", LVar "m") []
let%test _ = can_equal (LVar "n", LNum 0) []
let%test _ = can_equal (LVar "n", LSum [ LVar "m"; LNum 1 ]) []
let%test _ = not (can_equal (LVar "n", LSum [ LVar "n"; LNum 1 ]) [])

let%test _ =
  not (can_equal (LVar "n", LSum [ LVar "m"; LNum 1 ]) [ (LVar "n", LNum 0) ])

let%test _ = not (can_equal (LSum [ LVar "n"; LNum 1 ], LNum 0) [])
let%test _ = can_equal (LSum [ LVar "n"; LNum 1 ], LSum [ LVar "m"; LNum 1 ]) []

let%test _ =
  not (can_equal (LVar "n", LNum 0) [ (LVar "n", LSum [ LVar "n'"; LNum 1 ]) ])

let%test _ =
  can_equal
    (LVar "n", LSum [ LVar "n''"; LNum 1 ])
    [ (LVar "n", LSum [ LVar "n'"; LNum 1 ]) ]
