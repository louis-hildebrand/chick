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
           let expected = arrow Nat Nat in
           let actual = synth ctxt t in
           assert_equal expected actual );
         ( "count_down" >:: fun _ ->
           let count_down =
             Fix
               ( "cnt",
                 Lam
                   ( "n",
                     NatMatch
                       ( Var "n",
                         Nil,
                         "m",
                         Cons
                           ( Syn (Var "m"),
                             Syn (Var "n"),
                             Syn (App (Var "cnt", Syn (Var "m"))) ) ) ) )
           in
           let typ = Pi ("n", Nat, Vec (Syn (Var "n"))) in
           check Context.empty count_down typ );
         ( "map" >:: fun _ ->
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
                                   ( Syn (Var "m"),
                                     Syn (App (Var "f", Syn (Var "x"))),
                                     Syn
                                       (apps (Var "map")
                                          [
                                            Syn (Var "m");
                                            Syn (Var "f");
                                            Syn (Var "xs");
                                          ]) ) ) ) ) ) )
           in
           let typ =
             Pi
               ( "n",
                 Nat,
                 arrows
                   [ Vec (Syn (Var "n")); arrow Nat Nat; Vec (Syn (Var "n")) ]
               )
           in
           check Context.empty map typ );
         ( "foldl" >:: fun _ ->
           let foldl =
             Fix
               ( "foldl",
                 Lam
                   ( "n",
                     Lam
                       ( "v",
                         Lam
                           ( "z",
                             Lam
                               ( "f",
                                 VecMatch
                                   ( Var "v",
                                     Syn (Var "z"),
                                     "m",
                                     "x",
                                     "xs",
                                     Syn
                                       (apps (Var "foldl")
                                          [
                                            Syn (Var "m");
                                            Syn (Var "xs");
                                            Syn
                                              (apps (Var "f")
                                                 [
                                                   Syn (Var "z"); Syn (Var "x");
                                                 ]);
                                            Syn (Var "f");
                                          ]) ) ) ) ) ) )
           in
           let typ =
             Pi
               ( "n",
                 Nat,
                 arrows
                   [ Vec (Syn (Var "n")); Nat; arrows [ Nat; Nat; Nat ]; Nat ]
               )
           in
           check Context.empty foldl typ );
         ( "foldr" >:: fun _ ->
           let foldr =
             Fix
               ( "foldr",
                 Lam
                   ( "n",
                     Lam
                       ( "v",
                         Lam
                           ( "z",
                             Lam
                               ( "f",
                                 VecMatch
                                   ( Var "v",
                                     Syn (Var "z"),
                                     "m",
                                     "x",
                                     "xs",
                                     Syn
                                       (apps (Var "f")
                                          [
                                            Syn (Var "x");
                                            Syn
                                              (apps (Var "foldr")
                                                 [
                                                   Syn (Var "m");
                                                   Syn (Var "xs");
                                                   Syn (Var "z");
                                                   Syn (Var "f");
                                                 ]);
                                          ]) ) ) ) ) ) )
           in
           let typ =
             Pi
               ( "n",
                 Nat,
                 arrows
                   [ Vec (Syn (Var "n")); Nat; arrows [ Nat; Nat; Nat ]; Nat ]
               )
           in
           check Context.empty foldr typ );
         ( "free_var" >:: fun _ ->
           assert_raises (Type_error "free variable") (fun _ ->
               synth Context.empty (Var "x")) );
       ]

let _ = run_test_tt_main tests
