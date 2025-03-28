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
           let t = App (Var "f", Sum [ sv "n"; Num 1 ]) in
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
                         Cons (sv "m", sv "n", Syn (App (Var "cnt", sv "m"))) )
                   ) )
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
                                   ( sv "m",
                                     Syn (App (Var "f", sv "x")),
                                     Syn
                                       (apps (Var "map")
                                          [ sv "m"; sv "f"; sv "xs" ]) ) ) ) )
                   ) )
           in
           let typ =
             Pi ("n", Nat, arrows [ Vec (sv "n"); arrow Nat Nat; Vec (sv "n") ])
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
                                            sv "m";
                                            sv "xs";
                                            Syn
                                              (apps (Var "f")
                                                 [ sv "z"; sv "x" ]);
                                            sv "f";
                                          ]) ) ) ) ) ) )
           in
           let typ =
             Pi
               ( "n",
                 Nat,
                 arrows [ Vec (sv "n"); Nat; arrows [ Nat; Nat; Nat ]; Nat ] )
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
                                     sv "z",
                                     "m",
                                     "x",
                                     "xs",
                                     Syn
                                       (apps (Var "f")
                                          [
                                            sv "x";
                                            Syn
                                              (apps (Var "foldr")
                                                 [
                                                   sv "m";
                                                   sv "xs";
                                                   sv "z";
                                                   sv "f";
                                                 ]);
                                          ]) ) ) ) ) ) )
           in
           let typ =
             Pi
               ( "n",
                 Nat,
                 arrows [ Vec (sv "n"); Nat; arrows [ Nat; Nat; Nat ]; Nat ] )
           in
           check Context.empty foldr typ );
         ( "zip_with" >:: fun _ ->
           let zip_with =
             Fix
               ( "zip_with",
                 Lam
                   ( "n",
                     Lam
                       ( "v1",
                         Lam
                           ( "v2",
                             Lam
                               ( "f",
                                 NatMatch
                                   ( Var "n",
                                     Nil,
                                     "m",
                                     Cons
                                       ( sv "m",
                                         Syn
                                           (apps (Var "f")
                                              [
                                                Syn (Head (sv "m", Var "v1"));
                                                Syn (Head (sv "m", Var "v2"));
                                              ]),
                                         Syn
                                           (apps (Var "zip_with")
                                              [
                                                sv "m"; sv "xs"; sv "ys"; sv "f";
                                              ]) ) ) ) ) ) ) )
           in
           let typ =
             Pi
               ( "n",
                 Nat,
                 arrows
                   [
                     Vec (sv "n");
                     Vec (sv "n");
                     arrows [ Nat; Nat; Nat ];
                     Vec (sv "n");
                   ] )
           in
           check Context.empty zip_with typ );
         ( "concat" >:: fun _ ->
           let concat =
             Fix
               ( "concat",
                 Lam
                   ( "n",
                     Lam
                       ( "m",
                         Lam
                           ( "v1",
                             Lam
                               ( "v2",
                                 VecMatch
                                   ( Var "v1",
                                     Syn (Var "v2"),
                                     "n'",
                                     "x",
                                     "xs",
                                     Cons
                                       ( Sum [ sv "n'"; sv "m" ],
                                         sv "x",
                                         Syn
                                           (apps (Var "concat")
                                              [
                                                sv "n'";
                                                sv "m";
                                                sv "xs";
                                                sv "v2";
                                              ]) ) ) ) ) ) ) )
           in
           let typ =
             Pi
               ( "n",
                 Nat,
                 Pi
                   ( "m",
                     Nat,
                     arrows
                       [
                         Vec (sv "n");
                         Vec (sv "m");
                         Vec (Sum [ sv "n"; sv "m" ]);
                       ] ) )
           in
           check Context.empty concat typ );
         ( "take" >:: fun _ ->
           let take =
             Fix
               ( "take",
                 Lam
                   ( "n",
                     Lam
                       ( "k",
                         Lam
                           ( "v",
                             NatMatch
                               ( Var "k",
                                 Nil,
                                 "k'",
                                 Cons
                                   ( sv "k'",
                                     sv "x",
                                     Syn
                                       (apps (Var "take")
                                          [ sv "n"; sv "k'"; sv "xs" ]) ) ) ) )
                   ) )
           in
           let typ =
             Pi
               ( "n",
                 Nat,
                 Pi
                   ( "k",
                     Nat,
                     arrow (Vec (Sum [ sv "n"; sv "k" ])) (Vec (sv "k")) ) )
           in
           check Context.empty take typ );
         ( "free_var" >:: fun _ ->
           assert_raises (Type_error "free variable") (fun _ ->
               synth Context.empty (Var "x")) );
       ]

let _ = run_test_tt_main tests
