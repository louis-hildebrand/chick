open OUnit2
open Chick.Typecheck
open Chick.Syntax

let head =
  (*
    let head : Pi (n:Nat) . Vec (n+1) -> Nat =
      \n.\v.
        match v with
        | nil -> unreachable
        | cons n x xs -> x
  *)
  {
    name = "head";
    body =
      Lam
        ("n", Lam ("v", VecMatch (Var "v", None, Some ("n", "x", "xs", sv "x"))));
    typ = Pi ("n", Nat, arrow (Vec (Sum [ sv "n"; Num 1 ])) Nat);
  }

let test_head _ = check_program [ head ]

let tail =
  (*
    let tail : Pi (n:Nat) . Vec (n+1) -> Vec n =
      \n.\v.
        match v with
        | nil -> unreachable
        | cons n x xs -> xs
  *)
  {
    name = "tail";
    body =
      Lam
        ( "n",
          Lam ("v", VecMatch (Var "v", None, Some ("n", "x", "xs", sv "xs"))) );
    typ = Pi ("n", Nat, arrow (Vec (Sum [ sv "n"; Num 1 ])) (Vec (sv "n")));
  }

let test_tail _ = check_program [ tail ]

let count_down =
  (*
    let count_down : Pi n:Nat . Vec n =
      fix count_down.\n.
        match n with
        | 0 -> nil
        | m + 1 -> cons m m (count_down m)
  *)
  {
    name = "count_down";
    body =
      Fix
        ( "count_down",
          Lam
            ( "n",
              NatMatch
                ( Var "n",
                  Some Nil,
                  Some
                    ( "m",
                      Cons (sv "m", sv "m", Syn (App (Var "count_down", sv "m")))
                    ) ) ) );
    typ = Pi ("n", Nat, Vec (Syn (Var "n")));
  }

let test_count_down _ = check_program [ count_down ]

let test_count_down_wrong_base_case _ =
  let count_down =
    (*
      let count_down : Pi n:Nat . Vec n =
        fix count_down.\n.
          match n with
          | 0     -> cons 0 0 nil
          | m + 1 -> cons m m (count_down m)
    *)
    {
      name = "count_down";
      body =
        Fix
          ( "count_down",
            Lam
              ( "n",
                NatMatch
                  ( Var "n",
                    Some (Cons (Num 0, Num 0, Nil)),
                    Some
                      ( "m",
                        Cons
                          (sv "m", sv "m", Syn (App (Var "count_down", sv "m")))
                      ) ) ) );
      typ = Pi ("n", Nat, Vec (Syn (Var "n")));
    }
  in
  assert_raises
    (Type_error "Term 'cons 0 0 nil' does not have the expected type 'Vec n'.")
    (fun _ -> check_program [ count_down ])

let test_count_down_wrong_step_case _ =
  let count_down =
    (*
      let count_down : Pi n:Nat . Vec n =
        fix count_down.\n.
          match n with
          | 0     -> nil
          | m + 1 -> cons n m (count_down n)
    *)
    {
      name = "count_down";
      body =
        Fix
          ( "count_down",
            Lam
              ( "n",
                NatMatch
                  ( Var "n",
                    Some Nil,
                    Some
                      ( "m",
                        Cons
                          (sv "n", sv "m", Syn (App (Var "count_down", sv "n")))
                      ) ) ) );
      typ = Pi ("n", Nat, Vec (Syn (Var "n")));
    }
  in
  assert_raises
    (Type_error
       "Term 'cons n m (count_down n)' does not have the expected type 'Vec n'.")
    (fun _ -> check_program [ count_down ])

let test_count_up _ =
  (*
    let count_up_from : Pi n:Nat . Pi _:Nat . Vec n =
      fix cnt.\n.\z.
        match n with
        | 0 -> nil
        | n' + 1 -> cons n' z (cnt n' (z + 1))
    let count_up : Pi n:Nat . Vec n =
      \n.count_up_from n 0
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
                        Some Nil,
                        Some
                          ( "n'",
                            Cons
                              ( sv "n'",
                                sv "z",
                                Syn
                                  (apps (Var "cnt")
                                     [ sv "n'"; Sum [ sv "z"; Num 1 ] ]) ) ) )
                  ) ) );
      typ = Pi ("n", Nat, arrow Nat (Vec (sv "n")));
    }
  in
  let count_up =
    {
      name = "count_up";
      body = Lam ("n", Syn (apps (Var "count_up_from") [ sv "n"; Num 0 ]));
      typ = Pi ("n", Nat, Vec (sv "n"));
    }
  in
  check_program [ count_up_from; count_up ]

let test_map _ =
  let map =
    {
      name = "map";
      body =
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
                            Some Nil,
                            Some
                              ( "m",
                                "x",
                                "xs",
                                Cons
                                  ( sv "m",
                                    Syn (App (Var "f", sv "x")),
                                    Syn
                                      (apps (Var "map")
                                         [ sv "m"; sv "xs"; sv "f" ]) ) ) ) ) )
              ) );
      typ = Pi ("n", Nat, arrows [ Vec (sv "n"); arrow Nat Nat; Vec (sv "n") ]);
    }
  in
  check_program [ map ]

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
                              Some (Syn (Var "z")),
                              Some
                                ( "m",
                                  "x",
                                  "xs",
                                  Syn
                                    (apps (Var "foldl")
                                       [
                                         sv "m";
                                         sv "xs";
                                         Syn (apps (Var "f") [ sv "z"; sv "x" ]);
                                         sv "f";
                                       ]) ) ) ) ) ) ) );
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
    {
      name = "foldr";
      body =
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
                                Some (sv "z"),
                                Some
                                  ( "m",
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
                                         ]) ) ) ) ) ) ) );
      typ =
        Pi
          ("n", Nat, arrows [ Vec (sv "n"); Nat; arrows [ Nat; Nat; Nat ]; Nat ]);
    }
  in
  check_program [ foldr ]

let concat =
  {
    name = "concat";
    body =
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
                              Some (Syn (Var "v2")),
                              Some
                                ( "n'",
                                  "x",
                                  "xs",
                                  Cons
                                    ( Sum [ sv "n'"; sv "m" ],
                                      sv "x",
                                      Syn
                                        (apps (Var "concat")
                                           [ sv "n'"; sv "m"; sv "xs"; sv "v2" ])
                                    ) ) ) ) ) ) ) );
    typ =
      Pi
        ( "n",
          Nat,
          Pi
            ( "m",
              Nat,
              arrows
                [ Vec (sv "n"); Vec (sv "m"); Vec (Sum [ sv "n"; sv "m" ]) ] )
        );
  }

let test_concat _ =
  let example_use_0 =
    (* let ex0 : Vec 0 = concat 0 0 nil nil *)
    {
      name = "ex0";
      body = Syn (apps (Var "concat") [ Num 0; Num 0; Nil; Nil ]);
      typ = Vec (Num 0);
    }
  in
  let n = { name = "n"; body = Fix ("n", sv "n"); typ = Nat } in
  let m = { name = "m"; body = Fix ("n", sv "n"); typ = Nat } in
  let example_use_1 =
    (* let ex1 : Vec (n+m) = concat n m (count_down n) (count_down m) *)
    {
      name = "ex1";
      body =
        Syn
          (apps (Var "concat")
             [
               sv "n";
               sv "m";
               Syn (App (Var "count_down", sv "n"));
               Syn (App (Var "count_down", sv "m"));
             ]);
      typ = Vec (Sum [ sv "n"; sv "m" ]);
    }
  in
  check_program [ count_down; concat; example_use_0; n; m; example_use_1 ]

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
                              Some Nil,
                              Some
                                ( "m",
                                  Cons
                                    ( sv "m",
                                      Syn
                                        (apps (Var "f")
                                           [
                                             Syn
                                               (apps (Var "head")
                                                  [ sv "m"; sv "v1" ]);
                                             Syn
                                               (apps (Var "head")
                                                  [ sv "m"; sv "v2" ]);
                                           ]),
                                      Syn
                                        (apps (Var "zip_with")
                                           [
                                             sv "m";
                                             Syn
                                               (apps (Var "tail")
                                                  [ sv "m"; sv "v1" ]);
                                             Syn
                                               (apps (Var "tail")
                                                  [ sv "m"; sv "v2" ]);
                                             sv "f";
                                           ]) ) ) ) ) ) ) ) );
    typ =
      Pi
        ( "n",
          Nat,
          arrows
            [
              Vec (sv "n"); Vec (sv "n"); arrows [ Nat; Nat; Nat ]; Vec (sv "n");
            ] );
  }

(* TODO: Also test a version of zip_with that uses nested vmatch rather than head/tail? *)

let test_zip_with _ =
  let plus = Lam ("a", Lam ("b", Sum [ sv "a"; sv "b" ])) in
  let example_use_0 =
    (* let ex0 : Vec 0 = zip_with 0 nil nil (+) *)
    {
      name = "ex0";
      body = Syn (apps (Var "zip_with") [ Num 0; Nil; Nil; plus ]);
      typ = Vec (Num 0);
    }
  in
  let n = { name = "n"; body = Fix ("x", sv "x"); typ = Nat } in
  let m = { name = "m"; body = Fix ("x", sv "x"); typ = Nat } in
  let example_use_1 =
    (* let ex1 : Vec n = zip_with n (count_down n) (count_down n) (+) *)
    {
      name = "ex1";
      body =
        Syn
          (apps (Var "zip_with")
             [
               sv "n";
               Syn (App (Var "count_down", sv "n"));
               Syn (App (Var "count_down", sv "n"));
               plus;
             ]);
      typ = Vec (sv "n");
    }
  in
  let example_use_2 =
    (*
      let ex2 : Vec (n+m+1) =
        zip_with
          (1 + m + n)
          (concat (n+1) m (count_down (n + 1)) (count_down m))
          (concat (n+m) 1 (count_down (n + m)) (count_down 1))
          (+)
    *)
    {
      name = "ex2";
      body =
        Syn
          (apps (Var "zip_with")
             [
               Sum [ Num 1; sv "m"; sv "n" ];
               Syn
                 (apps (Var "concat")
                    [
                      Sum [ sv "n"; Num 1 ];
                      sv "m";
                      Syn (App (Var "count_down", Sum [ sv "n"; Num 1 ]));
                      Syn (App (Var "count_down", sv "m"));
                    ]);
               Syn
                 (apps (Var "concat")
                    [
                      Sum [ sv "n"; sv "m" ];
                      Num 1;
                      Syn (App (Var "count_down", Sum [ sv "n"; sv "m" ]));
                      Syn (App (Var "count_down", Num 1));
                    ]);
               plus;
             ]);
      typ = Vec (Sum [ sv "n"; sv "m"; Num 1 ]);
    }
  in
  check_program
    [
      head;
      tail;
      count_down;
      concat;
      zip_with;
      example_use_0;
      n;
      m;
      example_use_1;
      example_use_2;
    ]

let test_zip_with_wrong_size_0_vs_1 _ =
  let plus = Lam ("a", Lam ("b", Sum [ sv "a"; sv "b" ])) in
  let v0 = { name = "v0"; body = Nil; typ = Vec (Num 0) } in
  let v1 =
    { name = "v1"; body = Cons (Num 0, Num 42, Nil); typ = Vec (Num 1) }
  in
  let zipped0 =
    {
      name = "zipped";
      body = Syn (apps (Var "zip_with") [ Num 0; sv "v0"; sv "v1"; plus ]);
      typ = Vec (Num 0);
    }
  in
  let zipped1 =
    {
      name = "zipped";
      body = Syn (apps (Var "zip_with") [ Num 1; sv "v0"; sv "v1"; plus ]);
      typ = Vec (Num 1);
    }
  in
  assert_raises
    (Type_error "Term 'v1' does not have the expected type 'Vec 0'.") (fun _ ->
      check_program [ head; tail; zip_with; v0; v1; zipped0 ]);
  assert_raises
    (Type_error "Term 'v0' does not have the expected type 'Vec 1'.") (fun _ ->
      check_program [ head; tail; zip_with; v0; v1; zipped1 ])

let test_zip_with_wrong_size_n_vs_m _ =
  let plus = Lam ("a", Lam ("b", Sum [ sv "a"; sv "b" ])) in
  let ex0 =
    (*
      let sum_any : Pi n:Nat . Pi m:Nat . Vec n -> Vec m -> Vec n =
        \n.\m.\v0.\v1.
          zip_with n v0 v1 (+)
    *)
    {
      name = "sum_any";
      body =
        Lam
          ( "n",
            Lam
              ( "m",
                Lam
                  ( "v0",
                    Lam
                      ( "v1",
                        Syn
                          (apps (Var "zip_with")
                             [ sv "n"; sv "v0"; sv "v1"; plus ]) ) ) ) );
      typ =
        Pi
          ( "n",
            Nat,
            Pi ("m", Nat, arrows [ Vec (sv "n"); Vec (sv "m"); Vec (sv "n") ])
          );
    }
  in
  let ex1 =
    (*
      let sum_any : Pi n:Nat . Pi m:Nat . Vec n -> Vec m -> Vec m =
        \n.\m.\v0.\v1.
          zip_with m v0 v1 (+)
    *)
    {
      name = "sum_any";
      body =
        Lam
          ( "n",
            Lam
              ( "m",
                Lam
                  ( "v0",
                    Lam
                      ( "v1",
                        Syn
                          (apps (Var "zip_with")
                             [ sv "m"; sv "v0"; sv "v1"; plus ]) ) ) ) );
      typ =
        Pi
          ( "n",
            Nat,
            Pi ("m", Nat, arrows [ Vec (sv "n"); Vec (sv "m"); Vec (sv "m") ])
          );
    }
  in
  assert_raises
    (Type_error "Term 'v1' does not have the expected type 'Vec n'.") (fun _ ->
      check_program [ head; tail; zip_with; ex0 ]);
  assert_raises
    (Type_error "Term 'v0' does not have the expected type 'Vec m'.") (fun _ ->
      check_program [ head; tail; zip_with; ex1 ])

let take =
  (*
    let take : Pi n:Nat . Pi k:Nat . Pi _:Vec (k+n) . Vec k =
      fix take.\n.\k.\v.
        match k with
        | case 0      -> nil
        | case k' + 1 ->
            let x = head (n + k') v in
            let xs = tail (n + k') v in
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
                          Some Nil,
                          Some
                            ( "k'",
                              Cons
                                ( sv "k'",
                                  Syn
                                    (apps (Var "head")
                                       [ Sum [ sv "n"; sv "k'" ]; sv "v" ]),
                                  Syn
                                    (apps (Var "take")
                                       [
                                         sv "n";
                                         sv "k'";
                                         Syn
                                           (apps (Var "tail")
                                              [
                                                Sum [ sv "n"; sv "k'" ]; sv "v";
                                              ]);
                                       ]) ) ) ) ) ) ) );
    typ =
      Pi
        ( "n",
          Nat,
          Pi ("k", Nat, arrow (Vec (Sum [ sv "n"; sv "k" ])) (Vec (sv "k"))) );
  }

let test_take _ = check_program [ head; tail; take ]

let test_take_wrong_base_case _ =
  (*
    let take : Pi n:Nat . Pi k:Nat . Pi _:Vec (k+n) . Vec k =
      fix take.\n.\k.\v.
        match k with
        | case 0      -> v  // <-- WRONG!
        | case k' + 1 ->
            let x = head (n + k') v in
            let xs = tail (n + k') v in
            cons k' x (take n k' xs)
  *)
  let take =
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
                            Some (sv "v"),
                            Some
                              ( "k'",
                                Cons
                                  ( sv "k'",
                                    Syn
                                      (apps (Var "head")
                                         [ Sum [ sv "n"; sv "k'" ]; sv "v" ]),
                                    Syn
                                      (apps (Var "take")
                                         [
                                           sv "n";
                                           sv "k'";
                                           Syn
                                             (apps (Var "tail")
                                                [
                                                  Sum [ sv "n"; sv "k'" ];
                                                  sv "v";
                                                ]);
                                         ]) ) ) ) ) ) ) );
      typ =
        Pi
          ( "n",
            Nat,
            Pi ("k", Nat, arrow (Vec (Sum [ sv "n"; sv "k" ])) (Vec (sv "k")))
          );
    }
  in
  assert_raises (Type_error "Term 'v' does not have the expected type 'Vec k'.")
    (fun _ -> check_program [ take ])

let test_drop _ =
  (*
    let drop : Pi n:Nat . Pi k:Nat . Pi _:Vec (k+n) . Vec n =
      fix drop.\n.\k.\v.
        match k with
        | 0      -> v
        | k' + 1 -> drop n k' (tail (n + k') v)
  *)
  let drop =
    {
      name = "drop";
      body =
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
                            Some (sv "v"),
                            Some
                              ( "k'",
                                Syn
                                  (apps (Var "drop")
                                     [
                                       sv "n";
                                       sv "k'";
                                       Syn
                                         (apps (Var "tail")
                                            [ Sum [ sv "n"; sv "k'" ]; sv "v" ]);
                                     ]) ) ) ) ) ) );
      typ =
        Pi
          ( "n",
            Nat,
            Pi ("k", Nat, arrow (Vec (Sum [ sv "k"; sv "n" ])) (Vec (sv "n")))
          );
    }
  in
  check_program [ head; tail; drop ]

(*
  I actually made this mistake when writing the original code xD
  Maybe this would be a good example for the "Motivation" section of the
  presentation.
*)
let test_drop_wrong_base_case _ =
  let drop =
    {
      (*
        let drop : Pi n:Nat . Pi k:Nat . Pi _:Vec (k+n) . Vec n =
          fix drop.\n.\k.\v.
            match k with
            | 0      -> nil  // <-- WRONG!
            | k' + 1 -> drop n k' (tail (n + k' + 1) v)
      *)
      name = "drop";
      body =
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
                            Some Nil,
                            Some
                              ( "k'",
                                Syn
                                  (apps (Var "drop")
                                     [
                                       sv "n";
                                       sv "k'";
                                       Syn
                                         (apps (Var "tail")
                                            [
                                              Sum [ sv "n"; sv "k'"; Num 1 ];
                                              sv "v";
                                            ]);
                                     ]) ) ) ) ) ) );
      typ =
        Pi
          ( "n",
            Nat,
            Pi ("k", Nat, arrow (Vec (Sum [ sv "k"; sv "n" ])) (Vec (sv "n")))
          );
    }
  in
  assert_raises
    (Type_error "Term 'nil' does not have the expected type 'Vec n'.") (fun _ ->
      check_program [ head; tail; drop ])

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
                        Some (Num 0),
                        Some
                          ( "x'",
                            Sum
                              [
                                Syn (apps (Var "times") [ sv "x'"; sv "y" ]);
                                sv "y";
                              ] ) ) ) ) );
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
        Lam
          ( "n",
            Lam
              ( "v1",
                Lam
                  ( "v2",
                    Syn
                      (apps (Var "vec_sum")
                         [
                           sv "n";
                           Syn
                             (apps (Var "zip_with")
                                [ sv "n"; sv "v1"; sv "v2"; sv "times" ]);
                         ]) ) ) );
      typ = Pi ("n", Nat, arrows [ Vec (sv "n"); Vec (sv "n"); Nat ]);
    }
  in
  check_program [ head; tail; foldl; vec_sum; zip_with; times; dot ]

(* Here's how you can specify that a vector must have even length. *)
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
  check_program [ head; tail; take; first_half ]

let test_vmatch_unreachable_and_missing _ =
  let foo =
    (*
      let foo : Pi (n:Nat) . Vec n -> Vec n -> Vec n =
        fix foo.\n.\v1.\v2.
          vmatch v1 with
          | nil ->
            vmatch v2 with
            | nil -> nil
          | cons n' x xs ->
            vmatch v2 with
            | cons n' y ys ->
              cons n' (x + y) (foo n' xs ys)
    *)
    {
      name = "foo";
      body =
        Fix
          ( "foo",
            Lam
              ( "n",
                Lam
                  ( "v1",
                    Lam
                      ( "v2",
                        VecMatch
                          ( Var "v1",
                            Some (VecMatch (Var "v2", Some Nil, None)),
                            Some
                              ( "n'",
                                "x",
                                "xs",
                                VecMatch
                                  ( Var "v2",
                                    None,
                                    Some
                                      ( "n'",
                                        "y",
                                        "ys",
                                        Cons
                                          ( sv "n'",
                                            Sum [ sv "x"; sv "y" ],
                                            Syn
                                              (apps (Var "foo")
                                                 [ sv "n'"; sv "xs"; sv "ys" ])
                                          ) ) ) ) ) ) ) ) );
      typ = Pi ("n", Nat, arrows [ Vec (sv "n"); Vec (sv "n"); Vec (sv "n") ]);
    }
  in
  check_program [ foo ]

let test_vmatch_nil_case_reachable_but_missing _ =
  let unsafe_head =
    (*
      let head : Pi (n:Nat) . Vec n -> Nat =
        \n.\v.
          vmatch v with
          | nil -> unreachable
          | cons n' x xs -> x
    *)
    {
      name = "head";
      body =
        Lam
          ( "n",
            Lam ("v", VecMatch (Var "v", None, Some ("n'", "x", "xs", sv "x")))
          );
      typ = Pi ("n", Nat, arrow (Vec (sv "n")) Nat);
    }
  in
  assert_raises (Type_error "The nil branch is reachable but not implemented.")
    (fun _ -> check_program [ unsafe_head ])

let test_vmatch_nil_case_unreachable_but_implemented _ =
  let head =
    (*
      let head : Pi (n:Nat) . Vec (n+1) -> Nat =
        \n.\v.
          vmatch v with
          | nil -> 0
          | cons n' x xs -> x
    *)
    {
      name = "head";
      body =
        Lam
          ( "n",
            Lam
              ( "v",
                VecMatch (Var "v", Some (Num 0), Some ("n'", "x", "xs", sv "x"))
              ) );
      typ = Pi ("n", Nat, arrow (Vec (Sum [ sv "n"; Num 1 ])) Nat);
    }
  in
  assert_raises
    (Type_error
       "The nil branch is unreachable and should therefore be left \
        unimplemented.") (fun _ -> check_program [ head ])

let test_vmatch_cons_case_reachable_but_missing _ =
  let foo =
    (*
      let foo : Pi (n:Nat) . Vec n -> Nat =
        \n.\v.
          vmatch v with
          | nil -> 0
    *)
    {
      name = "foo";
      body = Lam ("n", Lam ("v", VecMatch (Var "v", Some (Num 0), None)));
      typ = Pi ("n", Nat, arrow (Vec (sv "n")) Nat);
    }
  in
  assert_raises (Type_error "The cons branch is reachable but not implemented.")
    (fun _ -> check_program [ foo ])

let test_vmatch_cons_case_unreachable_but_implemented _ =
  let foo =
    (*
      let foo : Pi (n:Nat) . Vec n -> Vec n -> Vec n =
        \n.\v1.\v2.
          vmatch v1 with
          | nil ->
            vmatch v2 with
            | nil -> nil
            | cons n' x xs -> cons n' x xs
          | cons n' x xs -> cons n' x xs
    *)
    {
      name = "foo";
      body =
        Lam
          ( "n",
            Lam
              ( "v1",
                Lam
                  ( "v2",
                    VecMatch
                      ( Var "v1",
                        Some
                          (VecMatch
                             ( Var "v2",
                               Some Nil,
                               Some
                                 ( "n'",
                                   "x",
                                   "xs",
                                   Cons (sv "n'", sv "x", sv "xs") ) )),
                        Some ("n'", "x", "xs", Cons (sv "n'", sv "x", sv "xs"))
                      ) ) ) );
      typ = Pi ("n", Nat, arrows [ Vec (sv "n"); Vec (sv "n"); Vec (sv "n") ]);
    }
  in
  assert_raises
    (Type_error
       "The cons branch is unreachable and should therefore be left \
        unimplemented.") (fun _ -> check_program [ foo ])

let tests =
  "typecheck"
  >::: [
         "head:ok" >:: test_head;
         "tail:ok" >:: test_tail;
         "count_down:ok" >:: test_count_down;
         "count_down:wrong base case" >:: test_count_down_wrong_base_case;
         "count_down:wrong step case" >:: test_count_down_wrong_step_case;
         "count_up:ok" >:: test_count_up;
         "map:ok" >:: test_map;
         "foldl:ok" >:: test_foldl;
         "foldr:ok" >:: test_foldr;
         "zip_with:ok" >:: test_zip_with;
         "zip_with:0 with 1" >:: test_zip_with_wrong_size_0_vs_1;
         "zip_with:n with m" >:: test_zip_with_wrong_size_n_vs_m;
         "concat:ok" >:: test_concat;
         "take:ok" >:: test_take;
         "take:wrong base case" >:: test_take_wrong_base_case;
         "drop:ok" >:: test_drop;
         "drop:wrong base case" >:: test_drop_wrong_base_case;
         "dot:ok" >:: test_dot;
         "first_half:ok" >:: test_first_half;
         "vmatch-unreachable-missing" >:: test_vmatch_unreachable_and_missing;
         "vmatch-nil-reachable-missing"
         >:: test_vmatch_nil_case_reachable_but_missing;
         "vmatch-nil-unreachable-implemented"
         >:: test_vmatch_nil_case_unreachable_but_implemented;
         "vmatch-cons-reachable-missing"
         >:: test_vmatch_cons_case_reachable_but_missing;
         "vmatch-cons-unreachable-implemented"
         >:: test_vmatch_cons_case_unreachable_but_implemented;
       ]

let _ = run_test_tt_main tests
