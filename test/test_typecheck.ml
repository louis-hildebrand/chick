open OUnit2
open Typecheck
open Syntax

let tests =
  "typecheck"
  >::: [
         ( "synth_success_no_dependent_types" >:: fun _ ->
           let ctxt =
             Context.of_seq
             @@ List.to_seq
                  [ ("f", Pi ("_", Nat, Pi ("_", Nat, Nat))); ("n", Nat) ]
           in
           let t = App (Var "f", Sum [ Syn (Var "n"); Num 1 ]) in
           let expected = Pi ("_", Nat, Nat) in
           let actual = synth ctxt t in
           assert_equal expected actual );
         ( "free_var" >:: fun _ ->
           assert_raises (Type_error "free variable") (fun _ ->
               synth Context.empty (Var "x")) );
       ]

let _ = run_test_tt_main tests
