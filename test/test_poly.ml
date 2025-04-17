open OUnit2
open Chick.Typecheck
open Chick.Syntax

let head_poly =
  (*
    let head_poly : Pi (n:Nat). Vec A (n + 1) -> A =
      \n.\v.
        match v with
        | nil -> unreachable
        | cons n x xs -> x
  *)
  {
    name = "head_poly";
    body =
      Lam
        ("n", Lam ("v", VecMatch (Var "v", None, Some ("n", "x", "xs", sv "x"))));
    typ =
      Pi
        ( "n",
          Nat,
          arrow (vec (Alpha "A") (LSum [ LVar "n"; LNum 1 ])) (Alpha "A") );
  }

let test_head_poly _ = check_program [ head_poly ]
let tests = "typecheck_poly" >::: [ "head_poly:ok" >:: test_head_poly ]
let _ = run_test_tt_main tests
