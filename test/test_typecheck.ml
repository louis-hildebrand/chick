open OUnit2
open Typecheck
open Syntax

(* TODO: Look for off-by-one errors here. *)
let test_count_down _ =
  let count_down =
    Fix
      ( "cnt",
        Lam
          ( "n",
            NatMatch
              ( Var "n",
                Nil,
                "m",
                Cons (sv "m", sv "n", Syn (App (Var "cnt", sv "m"))) ) ) )
  in
  let typ = Pi ("n", Nat, Vec (Syn (Var "n"))) in
  check Context.empty count_down typ

let test_count_up _ =
  (*
    let count_up_from : Pi n:Nat . Pi _:Nat . Vec n =
      fix cnt.\n.\z.
        match n with
        | 0 -> nil
        | n' + 1 -> cons n' z (cnt n' (z + 1))
    let count_up : Pi n:Nat . Vec n =
      count_up_from n 0
  *)
  let count_up_from =
    {
      name = "count_up_from";
      body =
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
                            Syn
                              (apps (Var "cnt")
                                 [ sv "n'"; Sum [ sv "z"; Num 1 ] ]) ) ) ) ) );
      typ = Pi ("n", Nat, arrow Nat (Vec (sv "n")));
    }
  in
  let count_up =
    {
      name = "count_up";
      body = Syn (apps (Var "count_up_from") [ sv "n"; Num 0 ]);
      typ = Pi ("n", Nat, Vec (sv "n"));
    }
  in
  check_program [ count_up_from; count_up ]

let test_map _ =
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
                            Syn (apps (Var "map") [ sv "m"; sv "f"; sv "xs" ])
                          ) ) ) ) ) )
  in
  let typ =
    Pi ("n", Nat, arrows [ Vec (sv "n"); arrow Nat Nat; Vec (sv "n") ])
  in
  check Context.empty map typ

let foldl =
  {
    name = "foldl";
    body =
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
                                     Syn (apps (Var "f") [ sv "z"; sv "x" ]);
                                     sv "f";
                                   ]) ) ) ) ) ) );
    typ =
      Pi ("n", Nat, arrows [ Vec (sv "n"); Nat; arrows [ Nat; Nat; Nat ]; Nat ]);
  }

let vec_sum =
  (*
    vec_sum : Pi n:Nat . Pi _:Vec n . Nat =
      \n.\v.
        foldl n v 0 (\a.\b.a + b)
  *)
  {
    name = "vec_sum";
    body =
      Lam
        ( "n",
          Lam
            ( "v",
              Syn
                (apps (Var "foldl")
                   [
                     sv "n";
                     sv "v";
                     Num 0;
                     Lam ("a", Lam ("b", Sum [ sv "a"; sv "b" ]));
                   ]) ) );
    typ = Pi ("n", Nat, arrow (Vec (sv "n")) Nat);
  }

let test_foldl _ = check_program [ foldl; vec_sum ]

let test_foldr _ =
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
                                        [ sv "m"; sv "xs"; sv "z"; sv "f" ]);
                                 ]) ) ) ) ) ) )
  in
  let typ =
    Pi ("n", Nat, arrows [ Vec (sv "n"); Nat; arrows [ Nat; Nat; Nat ]; Nat ])
  in
  check Context.empty foldr typ

let zip_with =
  {
    name = "zip_with";
    body =
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
                                       [ sv "m"; sv "xs"; sv "ys"; sv "f" ]) )
                            ) ) ) ) ) );
    typ =
      Pi
        ( "n",
          Nat,
          arrows
            [
              Vec (sv "n"); Vec (sv "n"); arrows [ Nat; Nat; Nat ]; Vec (sv "n");
            ] );
  }

let test_zip_with _ = check_program [ zip_with ]

let test_concat _ =
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
                                     [ sv "n'"; sv "m"; sv "xs"; sv "v2" ]) ) )
                      ) ) ) ) )
  in
  let typ =
    Pi
      ( "n",
        Nat,
        Pi
          ( "m",
            Nat,
            arrows [ Vec (sv "n"); Vec (sv "m"); Vec (Sum [ sv "n"; sv "m" ]) ]
          ) )
  in
  check Context.empty concat typ

let take =
  (*
    let take : Pi n:Nat . Pi k:Nat . Pi _:Vec (k+n) . Vec k =
      fix take.\n.\k.\v.
        match k with
        | case 0      -> v
        | case k' + 1 ->
            let x = head (n + k' + 1) v in
            let xs = tail (n + k' + 1) v in
            cons k' x (take n k' xs)
  *)
  {
    name = "take";
    body =
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
                          sv "v",
                          "k'",
                          Cons
                            ( sv "k'",
                              Syn
                                (Head (Sum [ sv "n"; sv "k'"; Num 1 ], Var "v")),
                              Syn
                                (apps (Var "take")
                                   [
                                     sv "n";
                                     sv "k'";
                                     Syn
                                       (Tail
                                          ( Sum [ sv "n"; sv "k'"; Num 1 ],
                                            Var "v" ));
                                   ]) ) ) ) ) ) );
    typ =
      Pi
        ( "n",
          Nat,
          Pi ("k", Nat, arrow (Vec (Sum [ sv "n"; sv "k" ])) (Vec (sv "k"))) );
  }

let test_take _ = check_program [ take ]

let test_take_wrong_base_case _ =
  (*
    let take : Pi n:Nat . Pi k:Nat . Pi _:Vec (k+n) . Vec k =
      fix take.\n.\k.\v.
        match k with
        | case 0      -> nil  // <-- WRONG!
        | case k' + 1 ->
            let x = head (n + k' + 1) v in
            let xs = tail (n + k' + 1) v in
            cons k' x (take n k' xs)
  *)
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
                            Syn (Head (Sum [ sv "n"; sv "k'"; Num 1 ], Var "v")),
                            Syn
                              (apps (Var "take")
                                 [
                                   sv "n";
                                   sv "k'";
                                   Syn
                                     (Tail
                                        (Sum [ sv "n"; sv "k'"; Num 1 ], Var "v"));
                                 ]) ) ) ) ) ) )
  in
  let typ =
    Pi
      ( "n",
        Nat,
        Pi ("k", Nat, arrow (Vec (Sum [ sv "n"; sv "k" ])) (Vec (sv "k"))) )
  in
  assert_raises
    (Type_error "Term 'Nil' does not have the expected type 'Vec n'.") (fun _ ->
      check Context.empty take typ)

let test_drop _ =
  (*
    let drop : Pi n:Nat . Pi k:Nat . Pi _:Vec (k+n) . Vec n =
      fix drop.\n.\k.\v.
        match k with
        | 0      -> v
        | k' + 1 -> drop n k' (tail (n + k' + 1) v)
  *)
  let drop =
    Fix
      ( "drop",
        Lam
          ( "n",
            Lam
              ( "k",
                Lam
                  ( "v",
                    NatMatch
                      ( Var "k",
                        sv "v",
                        "k'",
                        Syn
                          (apps (Var "drop")
                             [
                               sv "n";
                               sv "k'";
                               Syn
                                 (Tail (Sum [ sv "n"; sv "k'"; Num 1 ], Var "v"));
                             ]) ) ) ) ) )
  in
  let typ =
    Pi
      ( "n",
        Nat,
        Pi ("k", Nat, arrow (Vec (Sum [ sv "k"; sv "n" ])) (Vec (sv "n"))) )
  in
  check Context.empty drop typ

(*
  I actually made this mistake when writing the original code xD
  Maybe this would be a good example for the "Motivation" section of the
  presentation.
*)
let test_drop_wrong_base_case _ =
  (*
    let drop : Pi n:Nat . Pi k:Nat . Pi _:Vec (k+n) . Vec n =
      fix drop.\n.\k.\v.
        match k with
        | 0      -> nil  // <-- WRONG!
        | k' + 1 -> drop n k' (tail (n + k' + 1) v)
  *)
  let drop =
    Fix
      ( "drop",
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
                        Syn
                          (apps (Var "drop")
                             [
                               sv "n";
                               sv "k'";
                               Syn
                                 (Tail (Sum [ sv "n"; sv "k'"; Num 1 ], Var "v"));
                             ]) ) ) ) ) )
  in
  let typ =
    Pi
      ( "n",
        Nat,
        Pi ("k", Nat, arrow (Vec (Sum [ sv "k"; sv "n" ])) (Vec (sv "n"))) )
  in
  assert_raises
    (Type_error "Term 'Nil' does not have the expected type 'Vec n'.") (fun _ ->
      check Context.empty drop typ)

let test_dot _ =
  let times =
    (*
      let times : Nat -> Nat -> Nat =
        fix times.\x.\y.
          match x with
          | 0 -> 0
          | x' + 1 -> (times x' y) + y
    *)
    {
      name = "times";
      body =
        Fix
          ( "times",
            Lam
              ( "x",
                Lam
                  ( "y",
                    NatMatch
                      ( Var "x",
                        Num 0,
                        "x'",
                        Sum
                          [
                            Syn (apps (Var "times") [ sv "x'"; sv "y" ]); sv "y";
                          ] ) ) ) );
      typ = arrows [ Nat; Nat; Nat ];
    }
  in
  let dot =
    (*
      let dot : Pi n:Nat . Vec n -> Vec n -> Nat =
        \n.\v1.\v2.
          vec_sum n (zip_with n v1 v2 times)
    *)
    {
      name = "dot";
      body =
        Syn
          (apps (Var "vec_sum")
             [
               sv "n";
               Syn
                 (apps (Var "zip_with")
                    [ sv "n"; sv "v1"; sv "v2"; sv "times" ]);
             ]);
      typ = Pi ("n", Nat, arrows [ Vec (sv "n"); Vec (sv "n"); Nat ]);
    }
  in
  check_program [ foldl; vec_sum; zip_with; times; dot ]

let test_first_half _ =
  let first_half =
    (*
      let first_half : Pi n:Nat . Vec (n+n) -> Vec n =
        \n.\v.take n n v
    *)
    {
      name = "first_half";
      body =
        Lam ("n", Lam ("v", Syn (apps (Var "take") [ sv "n"; sv "n"; sv "v" ])));
      typ = Pi ("n", Nat, arrow (Vec (Sum [ sv "n"; sv "n" ])) (Vec (sv "n")));
    }
  in
  check_program [ take; first_half ]

let tests =
  "typecheck"
  >::: [
         "count_down" >:: test_count_down;
         "count_up" >:: test_count_up;
         "map" >:: test_map;
         "foldl" >:: test_foldl;
         "foldr" >:: test_foldr;
         "zip_with" >:: test_zip_with;
         "concat" >:: test_concat;
         "take" >:: test_take;
         "take_wrong_base_case" >:: test_take_wrong_base_case;
         "drop" >:: test_drop;
         "drop_wrong_base_case" >:: test_drop_wrong_base_case;
         "dot" >:: test_dot;
         "first_half" >:: test_first_half;
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
         ( "free_var" >:: fun _ ->
           assert_raises (Type_error "free variable") (fun _ ->
               synth Context.empty (Var "x")) );
       ]

let _ = run_test_tt_main tests
