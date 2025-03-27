open OUnit2
open Typecheck

let tests =
  "test suite for typecheck"
  >::: [
         ( "foo" >:: fun _ ->
           assert_equal "Hello there!" (foo ()) ~printer:(fun x -> x) );
       ]

let _ = run_test_tt_main tests
