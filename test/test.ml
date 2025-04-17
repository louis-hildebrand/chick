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
    typ = Pi ("n", Nat, arrow (vec Nat (LSum [ LVar "n"; LNum 1 ])) Nat);
  }

let test_head _ = check_program [ head ]

let head_bool =
  (*
    let head : Pi (n:Nat) . Vec Bool (n+1) -> Bool =
      \n.\v.
        match v with
        | nil -> unreachable
        | cons n x xs -> x
  *)
  {
    name = "head_bool";
    body = head.body;
    typ = Pi ("n", Nat, arrow (vec Bool (LSum [ LVar "n"; LNum 1 ])) Bool);
  }

let test_head_bool _ = check_program [ head_bool ]

let head_vec =
  (*
    let head : Pi (n:Nat) . Vec (Vec Bool n) (n+1) -> Vec Bool n =
      \n.\v.
        match v with
        | nil -> unreachable
        | cons n x xs -> x
  *)
  {
    name = "head_vec";
    body = head.body;
    typ =
      Pi
        ( "n",
          Nat,
          arrow
            (vec (vec Bool (LVar "n")) (LSum [ LVar "n"; LNum 1 ]))
            (vec Bool (LVar "n")) );
  }

let test_head_vec _ = check_program [ head_vec ]

let head_abs =
  (*
    let head : Pi (n:Nat) . Vec (Nat -> Bool) (n+1) -> (Nat -> Bool) =
      \n.\v.
        match v with
        | nil -> unreachable
        | cons n x xs -> x
  *)
  {
    name = "head_abs";
    body = head.body;
    typ =
      Pi
        ( "n",
          Nat,
          arrow
            (vec (arrow Nat Bool) (LSum [ LVar "n"; LNum 1 ]))
            (arrow Nat Bool) );
  }

let test_head_abs _ = check_program [ head_abs ]
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
    typ =
      Pi
        ( "n",
          Nat,
          arrow (vec Nat (LSum [ LVar "n"; LNum 1 ])) (vec Nat (LVar "n")) );
  }

let test_tail _ = check_program [ tail ]

let tail_bool =
  (*
    let tail : Pi (n:Nat) . Vec Bool (n+1) -> Vec Bool n =
      \n.\v.
        match v with
        | nil -> unreachable
        | cons n x xs -> xs
  *)
  {
    name = "tail_bool";
    body = tail.body;
    typ =
      Pi
        ( "n",
          Nat,
          arrow (vec Bool (LSum [ LVar "n"; LNum 1 ])) (vec Bool (LVar "n")) );
  }

let test_tail_bool _ = check_program [ tail_bool ]

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
                      Cons
                        (LVar "m", sv "m", Syn (App (Var "count_down", sv "m")))
                    ) ) ) );
    typ = Pi ("n", Nat, vec Nat (LVar "n"));
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
                    Some (Cons (LNum 0, Num 0, Nil)),
                    Some
                      ( "m",
                        Cons
                          ( LVar "m",
                            sv "m",
                            Syn (App (Var "count_down", sv "m")) ) ) ) ) );
      typ = Pi ("n", Nat, vec Nat (LVar "n"));
    }
  in
  assert_raises
    (Type_error
       "Term 'cons 0 0 nil' does not have the expected type 'Vec Nat n'.")
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
                          ( LVar "n",
                            sv "m",
                            Syn (App (Var "count_down", sv "n")) ) ) ) ) );
      typ = Pi ("n", Nat, vec Nat (LVar "n"));
    }
  in
  assert_raises
    (Type_error
       "Term 'cons n m (count_down n)' does not have the expected type 'Vec \
        Nat n'.") (fun _ -> check_program [ count_down ])

let test_count_up _ =
  (*
    let count_up_from : Pi n:Nat . Pi _:Nat . vec Nat n =
      fix cnt.\n.\z.
        match n with
        | 0 -> nil
        | n' + 1 -> cons n' z (cnt n' (z + 1))
    let count_up : Pi n:Nat . vec Nat n =
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
                              ( LVar "n'",
                                sv "z",
                                Syn
                                  (apps (Var "cnt")
                                     [ sv "n'"; Sum [ sv "z"; Num 1 ] ]) ) ) )
                  ) ) );
      typ = Pi ("n", Nat, arrow Nat (vec Nat (LVar "n")));
    }
  in
  let count_up =
    {
      name = "count_up";
      body = Lam ("n", Syn (apps (Var "count_up_from") [ sv "n"; Num 0 ]));
      typ = Pi ("n", Nat, vec Nat (LVar "n"));
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
                                  ( LVar "m",
                                    Syn (App (Var "f", sv "x")),
                                    Syn
                                      (apps (Var "map")
                                         [ sv "m"; sv "xs"; sv "f" ]) ) ) ) ) )
              ) );
      typ =
        Pi
          ( "n",
            Nat,
            arrows [ vec Nat (LVar "n"); arrow Nat Nat; vec Nat (LVar "n") ] );
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
      Pi
        ( "n",
          Nat,
          arrows [ vec Nat (LVar "n"); Nat; arrows [ Nat; Nat; Nat ]; Nat ] );
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
    typ = Pi ("n", Nat, arrow (vec Nat (LVar "n")) Nat);
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
          ( "n",
            Nat,
            arrows [ vec Nat (LVar "n"); Nat; arrows [ Nat; Nat; Nat ]; Nat ] );
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
                                    ( LSum [ LVar "n'"; LVar "m" ],
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
                [
                  vec Nat (LVar "n");
                  vec Nat (LVar "m");
                  vec Nat (LSum [ LVar "n"; LVar "m" ]);
                ] ) );
  }

let test_concat _ =
  let example_use_0 =
    (* let ex0 : Vec 0 = concat 0 0 nil nil *)
    {
      name = "ex0";
      body = Syn (apps (Var "concat") [ Num 0; Num 0; Nil; Nil ]);
      typ = vec Nat (LNum 0);
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
      typ = vec Nat (LSum [ LVar "n"; LVar "m" ]);
    }
  in
  check_program [ count_down; concat; example_use_0; n; m; example_use_1 ]

let test_reverse_with_concat _ =
  let reverse =
    (*
      let rev : Pi n:Nat . Vec n -> Vec n =
        fix rev.\n.\v.
          match v with 
          | nil -> nil
          | cons m x xs -> concat m 1 (rev m xs) (cons 0 x nil)
              *)
    {
      name = "rev";
      body =
        Fix
          ( "rev",
            Lam
              ( "n",
                Lam
                  ( "v",
                    VecMatch
                      ( Var "v",
                        Some Nil,
                        Some
                          ( "m",
                            "x",
                            "xs",
                            Syn
                              (apps (Var "concat")
                                 [
                                   sv "m";
                                   Num 1;
                                   Syn (apps (Var "rev") [ sv "m"; sv "xs" ]);
                                   Cons (LNum 0, sv "x", Nil);
                                 ]) ) ) ) ) );
      typ = Pi ("n", Nat, arrow (vec Nat (LVar "n")) (vec Nat (LVar "n")));
    }
  in
  check_program [ concat; reverse ]

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
                                    ( LVar "m",
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
              vec Nat (LVar "n");
              vec Nat (LVar "n");
              arrows [ Nat; Nat; Nat ];
              vec Nat (LVar "n");
            ] );
  }

(* TODO: Also test a version of zip_with that uses nested vmatch rather than head/tail? *)

let test_zip_with_head_tail _ =
  let plus = Lam ("a", Lam ("b", Sum [ sv "a"; sv "b" ])) in
  let example_use_0 =
    (* let ex0 : Vec 0 = zip_with 0 nil nil (+) *)
    {
      name = "ex0";
      body = Syn (apps (Var "zip_with") [ Num 0; Nil; Nil; plus ]);
      typ = vec Nat (LNum 0);
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
      typ = vec Nat (LVar "n");
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
      typ = vec Nat (LSum [ LVar "n"; LVar "m"; LNum 1 ]);
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

let test_zip_with_nested_vmatch _ =
  let zip_with =
    (*
      let zip_with : Pi (n:Nat) . Vec n -> Vec n -> (Nat -> Nat -> Nat) -> Vec n =
        fix zip_with.\n.\v1.\v2.\f.
          vmatch v1 with
          | nil ->
            // This nested vmatch probably isn't necessary, it's just to test
            // that omitting the cons branch works.
            vmatch v2 with
            | nil -> nil
          | cons n' x xs ->
            vmatch v2 with
            | cons n' y ys ->
              cons n' (f x y) (zip_with n' xs ys f)
    *)
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
                                              ( LVar "n'",
                                                Syn
                                                  (apps (Var "f")
                                                     [ sv "x"; sv "y" ]),
                                                Syn
                                                  (apps (Var "zip_with")
                                                     [
                                                       sv "n'";
                                                       sv "xs";
                                                       sv "ys";
                                                       sv "f";
                                                     ]) ) ) ) ) ) ) ) ) ) );
      typ =
        Pi
          ( "n",
            Nat,
            arrows
              [
                vec Nat (LVar "n");
                vec Nat (LVar "n");
                arrows [ Nat; Nat; Nat ];
                vec Nat (LVar "n");
              ] );
    }
  in
  check_program [ zip_with ]

let test_zip_with_wrong_size_0_vs_1 _ =
  let plus = Lam ("a", Lam ("b", Sum [ sv "a"; sv "b" ])) in
  let v0 = { name = "v0"; body = Nil; typ = vec Nat (LNum 0) } in
  let v1 =
    { name = "v1"; body = Cons (LNum 0, Num 42, Nil); typ = vec Nat (LNum 1) }
  in
  let zipped0 =
    {
      name = "zipped";
      body = Syn (apps (Var "zip_with") [ Num 0; sv "v0"; sv "v1"; plus ]);
      typ = vec Nat (LNum 0);
    }
  in
  let zipped1 =
    {
      name = "zipped";
      body = Syn (apps (Var "zip_with") [ Num 1; sv "v0"; sv "v1"; plus ]);
      typ = vec Nat (LNum 1);
    }
  in
  assert_raises
    (Type_error "Term 'v1' does not have the expected type 'Vec Nat 0'.")
    (fun _ -> check_program [ head; tail; zip_with; v0; v1; zipped0 ]);
  assert_raises
    (Type_error "Term 'v0' does not have the expected type 'Vec Nat 1'.")
    (fun _ -> check_program [ head; tail; zip_with; v0; v1; zipped1 ])

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
            Pi
              ( "m",
                Nat,
                arrows
                  [ vec Nat (LVar "n"); vec Nat (LVar "m"); vec Nat (LVar "n") ]
              ) );
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
            Pi
              ( "m",
                Nat,
                arrows
                  [ vec Nat (LVar "n"); vec Nat (LVar "m"); vec Nat (LVar "m") ]
              ) );
    }
  in
  assert_raises
    (Type_error "Term 'v1' does not have the expected type 'Vec Nat n'.")
    (fun _ -> check_program [ head; tail; zip_with; ex0 ]);
  assert_raises
    (Type_error "Term 'v0' does not have the expected type 'Vec Nat m'.")
    (fun _ -> check_program [ head; tail; zip_with; ex1 ])

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
                                ( LVar "k'",
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
          Pi
            ( "k",
              Nat,
              arrow (vec Nat (LSum [ LVar "n"; LVar "k" ])) (vec Nat (LVar "k"))
            ) );
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
                                  ( LVar "k'",
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
            Pi
              ( "k",
                Nat,
                arrow
                  (vec Nat (LSum [ LVar "n"; LVar "k" ]))
                  (vec Nat (LVar "k")) ) );
    }
  in
  assert_raises
    (Type_error "Term 'v' does not have the expected type 'Vec Nat k'.")
    (fun _ -> check_program [ take ])

let test_drop _ =
  (*
    let drop : Pi k:Nat . Pi n:Nat . Pi _:Vec (k+n) . Vec n =
      fix drop.\k.\n.\v.
        match k with
        | 0      -> v
        | k' + 1 -> drop k' n (tail (k' + n) v)
  *)
  let drop =
    {
      name = "drop";
      body =
        Fix
          ( "drop",
            Lam
              ( "k",
                Lam
                  ( "n",
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
                                       sv "k'";
                                       sv "n";
                                       Syn
                                         (apps (Var "tail")
                                            [ Sum [ sv "k'"; sv "n" ]; sv "v" ]);
                                     ]) ) ) ) ) ) );
      typ =
        Pi
          ( "k",
            Nat,
            Pi
              ( "n",
                Nat,
                arrow
                  (vec Nat (LSum [ LVar "k"; LVar "n" ]))
                  (vec Nat (LVar "n")) ) );
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
        let drop : Pi k:Nat . Pi n:Nat . Pi _:Vec (k+n) . Vec n =
          fix drop.\k.\n.\v.
            match k with
            | 0      -> nil  // <-- WRONG!
            | k' + 1 -> drop k' n (tail (k' + n) v)
      *)
      name = "drop";
      body =
        Fix
          ( "drop",
            Lam
              ( "k",
                Lam
                  ( "n",
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
                                       sv "k'";
                                       sv "n";
                                       Syn
                                         (apps (Var "tail")
                                            [ Sum [ sv "k'"; sv "n" ]; sv "v" ]);
                                     ]) ) ) ) ) ) );
      typ =
        Pi
          ( "k",
            Nat,
            Pi
              ( "n",
                Nat,
                arrow
                  (vec Nat (LSum [ LVar "k"; LVar "n" ]))
                  (vec Nat (LVar "n")) ) );
    }
  in
  assert_raises
    (Type_error "Term 'nil' does not have the expected type 'Vec Nat n'.")
    (fun _ -> check_program [ head; tail; drop ])

let test_drop_wrong_step_case _ =
  (*
    let drop : Pi k:Nat . Pi n:Nat . Pi _:Vec (k+n) . Vec n =
      fix drop.\k.\n.\v.
        match k with
        | 0      -> v
        | k' + 1 -> drop k n (tail (k' + n) v)  // <-- Should be drop k', not drop k
  *)
  let drop =
    {
      name = "drop";
      body =
        Fix
          ( "drop",
            Lam
              ( "k",
                Lam
                  ( "n",
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
                                       sv "k";
                                       sv "n";
                                       Syn
                                         (apps (Var "tail")
                                            [ Sum [ sv "k'"; sv "n" ]; sv "v" ]);
                                     ]) ) ) ) ) ) );
      typ =
        Pi
          ( "k",
            Nat,
            Pi
              ( "n",
                Nat,
                arrow
                  (vec Nat (LSum [ LVar "k"; LVar "n" ]))
                  (vec Nat (LVar "n")) ) );
    }
  in
  assert_raises
    (Type_error
       "Term 'tail (k' + n) v' does not have the expected type 'Vec Nat (k + \
        n)'.") (fun _ -> check_program [ head; tail; drop ])

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
      typ = Pi ("n", Nat, arrows [ vec Nat (LVar "n"); vec Nat (LVar "n"); Nat ]);
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
      typ =
        Pi
          ( "n",
            Nat,
            arrow (vec Nat (LSum [ LVar "n"; LVar "n" ])) (vec Nat (LVar "n"))
          );
    }
  in
  check_program [ head; tail; take; first_half ]

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
      typ = Pi ("n", Nat, arrow (vec Nat (LVar "n")) Nat);
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
      typ = Pi ("n", Nat, arrow (vec Nat (LSum [ LVar "n"; LNum 1 ])) Nat);
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
      typ = Pi ("n", Nat, arrow (vec Nat (LVar "n")) Nat);
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
                                   Cons (LVar "n'", sv "x", sv "xs") ) )),
                        Some ("n'", "x", "xs", Cons (LVar "n'", sv "x", sv "xs"))
                      ) ) ) );
      typ =
        Pi
          ( "n",
            Nat,
            arrows
              [ vec Nat (LVar "n"); vec Nat (LVar "n"); vec Nat (LVar "n") ] );
    }
  in
  assert_raises
    (Type_error
       "The cons branch is unreachable and should therefore be left \
        unimplemented.") (fun _ -> check_program [ foo ])

let test_shadow_toplevel _ =
  let foo1 = { name = "foo"; body = Lam ("x", sv "x"); typ = arrow Nat Nat } in
  let foo2 = { name = "foo"; body = Num 42; typ = Nat } in
  let bar = { name = "bar"; body = Sum [ sv "foo"; Num 0 ]; typ = Nat } in
  check_program [ foo1; foo2; bar ]

let test_shadow_in_nmatch _ =
  let foo =
    (*
      let foo : Nat -> Nat =
        \n.
          nmatch n with
          | 0 -> 0
          | n + 1 ->
            nmatch n with
            | 0 -> unreachable  // <-- But it is reachable!
            | n' + 1 -> 1
    *)
    {
      name = "foo";
      body =
        Lam
          ( "n",
            NatMatch
              ( Var "n",
                Some (Num 0),
                Some ("n", NatMatch (Var "n", None, Some ("n'", Num 1))) ) );
      typ = arrow Nat Nat;
    }
  in
  assert_raises (Type_error "The zero branch is reachable but not implemented.")
    (fun _ -> check_program [ foo ])

let test_shadow_in_vmatch _ =
  let foo =
    (*
      let foo : Pi (n:Nat) . Vec n -> Nat =
        \n.\v.
          vmatch v with
          | nil -> 0
          | cons n x xs ->
            nmatch n with
            | 0 -> unreachable  // <-- But it is reachable!
            | n' + 1 -> 1
    *)
    {
      name = "foo";
      body =
        Lam
          ( "n",
            Lam
              ( "v",
                VecMatch
                  ( Var "v",
                    Some (Num 0),
                    Some
                      ( "n",
                        "x",
                        "xs",
                        NatMatch (Var "n", None, Some ("n'", Num 1)) ) ) ) );
      typ = Pi ("n", Nat, arrow (vec Nat (LVar "n")) Nat);
    }
  in
  assert_raises (Type_error "The zero branch is reachable but not implemented.")
    (fun _ -> check_program [ foo ])

let test_is_empty _ =
  let is_empty =
    (*
      let is_empty : Pi (n:Nat) . Vec n -> Bool =
        \n.\v.
          vmatch v with
          | nil -> true
          | cons n' x xs -> false
    *)
    {
      name = "is_empty";
      body =
        Lam
          ( "n",
            Lam
              ("v", VecMatch (Var "v", Some True, Some ("n'", "x", "xs", False)))
          );
      typ = Pi ("n", Nat, arrow (vec Nat (LVar "n")) Bool);
    }
  in
  check_program [ is_empty ]

let test_bool2vec _ =
  let bool2vec =
    (*
      let bool2vec : Bool -> Vec 1 =
        \b.
          bmatch b with
          | true  -> [1]
          | false -> [0]
    *)
    {
      name = "bool2vec";
      body =
        Lam
          ( "b",
            BoolMatch
              (Var "b", Cons (LNum 0, Num 1, Nil), Cons (LNum 0, Num 0, Nil)) );
      typ = arrow Bool (vec Nat (LNum 1));
    }
  in
  let example0 =
    {
      name = "ex0";
      body = Syn (App (Var "bool2vec", False));
      typ = vec Nat (LNum 1);
    }
  in
  let example1 =
    {
      name = "ex1";
      body = Syn (App (Var "bool2vec", True));
      typ = vec Nat (LNum 1);
    }
  in
  let b = { name = "b"; body = True; typ = Bool } in
  let example2 =
    {
      name = "ex2";
      body = Syn (App (Var "bool2vec", sv "b"));
      typ = vec Nat (LNum 1);
    }
  in
  check_program [ bool2vec; example0; example1; b; example2 ]

let test_fst_nat _ =
  let fst =
    (*
      let fst_nat : (Nat * Nat) -> Nat =
        \p.pmatch p with
           | (y, _) -> y
    *)
    {
      name = "fst_nat";
      body = Lam ("p", PairMatch (Var "p", "y", "_", sv "y"));
      typ = arrow (times Nat Nat) Nat;
    }
  in
  let foo =
    { name = "foo"; body = Pair (Num 42, Num 99); typ = times Nat Nat }
  in
  let bar =
    { name = "bar"; body = Syn (App (Var "fst_nat", sv "foo")); typ = Nat }
  in
  check_program [ fst; foo; bar ]

let test_snd_nat _ =
  let snd =
    (*
      let snd_nat : (Nat * Nat) -> Nat =
        \p.pmatch p with
           | (_, y) -> y
    *)
    {
      name = "snd_nat";
      body = Lam ("p", PairMatch (Var "p", "_", "y", sv "y"));
      typ = arrow (times Nat Nat) Nat;
    }
  in
  let foo =
    { name = "foo"; body = Pair (Num 42, Num 99); typ = times Nat Nat }
  in
  let bar =
    { name = "bar"; body = Syn (App (Var "snd_nat", sv "foo")); typ = Nat }
  in
  check_program [ snd; foo; bar ]

let test_nat_bool_pair _ =
  let foo =
    { name = "foo"; body = Pair (Num 42, True); typ = times Nat Bool }
  in
  check_program [ foo ]

let test_dependent_vec_pair _ =
  let foo =
    {
      name = "foo";
      body = Pair (Num 42, Syn (App (Var "count_down", Num 42)));
      typ = Sigma ("n", Nat, vec Nat (LVar "n"));
    }
  in
  check_program [ count_down; foo ]

let test_dependent_vec_pair_wrong_size _ =
  let foo =
    {
      name = "foo";
      body = Pair (Num 42, Syn (App (Var "count_down", Num 43)));
      typ = Sigma ("n", Nat, vec Nat (LVar "n"));
    }
  in
  assert_raises
    (Type_error
       "Term 'count_down 43' does not have the expected type 'Vec Nat 42'.")
    (fun _ -> check_program [ count_down; foo ])

let test_snd_free_var _ =
  let foo =
    (*
      let foo : (Sigma (n:Nat) . Vec n) -> Vec n =
        \p.pmatch p with
           | (_, y) -> y
    *)
    {
      name = "foo";
      body = Lam ("p", PairMatch (Var "p", "_", "y", sv "y"));
      typ = arrow (Sigma ("n", Nat, vec Nat (LVar "n"))) (vec Nat (LVar "n"));
    }
  in
  assert_raises
    (Type_error
       "Type signature 'Pi (_:Sigma (n:Nat) . Vec Nat n) . Vec Nat n' has free \
        variables: [n].") (fun _ -> check_program [ foo ])

let test_pi_wrong_order _ =
  let foo =
    {
      name = "foo";
      body = Lam ("v", Lam ("n", sv "v"));
      typ = arrow (vec Nat (LVar "n")) (Pi ("n", Nat, vec Nat (LVar "n")));
    }
  in
  assert_raises
    (Type_error
       "Type signature 'Pi (_:Vec Nat n) . Pi (n:Nat) . Vec Nat n' has free \
        variables: [n].") (fun _ -> check_program [ foo ])

let test_filter _ =
  (* TODO: What if I used n instead of m for the output size? *)
  let filter =
    (*
      let filter : Pi (n:Nat) . Vec n -> (Nat -> Bool) -> (Sigma (m:Nat) . Vec m) =
        fix filter.\n.\v.\f.
          \vmatch v with
          | nil -> (0, nil)
          | cons n' x xs ->
            bmatch f x with
            | true ->
              pmatch (filter n' xs f) with
              | (m, xs') -> (m + 1, cons m x xs')
            | false ->
              filter n' xs f
    *)
    {
      name = "filter";
      body =
        Fix
          ( "filter",
            Lam
              ( "n",
                Lam
                  ( "v",
                    Lam
                      ( "f",
                        VecMatch
                          ( Var "v",
                            Some (Pair (Num 0, Nil)),
                            Some
                              ( "n'",
                                "x",
                                "xs",
                                BoolMatch
                                  ( App (Var "f", sv "x"),
                                    PairMatch
                                      ( apps (Var "filter")
                                          [ sv "n'"; sv "xs"; sv "f" ],
                                        "m",
                                        "xs'",
                                        Pair
                                          ( Sum [ sv "m"; Num 1 ],
                                            Cons (LVar "m", sv "x", sv "xs'") )
                                      ),
                                    Syn
                                      (apps (Var "filter")
                                         [ sv "n'"; sv "xs"; sv "f" ]) ) ) ) )
                  ) ) );
      typ =
        Pi
          ( "n",
            Nat,
            arrows
              [
                vec Nat (LVar "n");
                arrow Nat Bool;
                Sigma ("m", Nat, vec Nat (LVar "m"));
              ] );
    }
  in
  let example0 =
    (*
      let ex0 : Sigma (n:Nat) . Vec n =
        filter 42 (count_down 42) (\x.true)
    *)
    {
      name = "ex0";
      body =
        Syn
          (apps (Var "filter")
             [ Num 42; Syn (App (Var "count_down", Num 42)); Lam ("_", True) ]);
      typ = Sigma ("n", Nat, vec Nat (LVar "n"));
    }
  in
  check_program [ filter; count_down; example0 ]

let test_mask_filter _ =
  let mask_filter =
    (*
      let mask_filter : Pi (n:Nat) . Vec Nat n -> Vec Bool n -> (Sigma (m:Nat) . Vec Nat m) =
        fix mask_filter.\n.\v.\mask.
          vmatch v with
          | nil -> (0, nil)
          | cons k x xs ->
            bmatch (head k mask) with
            | true ->
              pmatch (mask_filter k xs (tail k mask)) with
              | (l, fs) -> (l + 1, cons l x fs)
            | false -> mask_filter k xs (tail k mask)
    *)
    {
      name = "mask_filter";
      body =
        Fix
          ( "mask_filter",
            Lam
              ( "n",
                Lam
                  ( "v",
                    Lam
                      ( "mask",
                        VecMatch
                          ( Var "v",
                            Some (Pair (Num 0, Nil)),
                            Some
                              ( "k",
                                "x",
                                "xs",
                                BoolMatch
                                  ( apps (Var "head_bool") [ sv "k"; sv "mask" ],
                                    PairMatch
                                      ( apps (Var "mask_filter")
                                          [
                                            sv "k";
                                            sv "xs";
                                            Syn
                                              (apps (Var "tail_bool")
                                                 [ sv "k"; sv "mask" ]);
                                          ],
                                        "l",
                                        "fs",
                                        Pair
                                          ( Sum [ sv "l"; Num 1 ],
                                            Cons (LVar "l", sv "x", sv "fs") )
                                      ),
                                    Syn
                                      (apps (Var "mask_filter")
                                         [
                                           sv "k";
                                           sv "xs";
                                           Syn
                                             (apps (Var "tail_bool")
                                                [ sv "k"; sv "mask" ]);
                                         ]) ) ) ) ) ) ) );
      typ =
        Pi
          ( "n",
            Nat,
            arrows
              [
                vec Nat (LVar "n");
                vec Bool (LVar "n");
                Sigma ("m", Nat, vec Nat (LVar "m"));
              ] );
    }
  in
  check_program [ head_bool; tail_bool; mask_filter ]

let zip =
  (*
    let zip : Pi n:Nat . Vec Nat n -> Vec Bool n -> Vec (Nat * Bool) n =
      fix zip.\n.\v1.\v2.
        vmatch v1 with
        | nil -> nil
        | cons m x xs -> cons m <x, head m v2> (zip m xs (tail m v2))
  *)
  {
    name = "zip";
    body =
      Fix
        ( "zip",
          Lam
            ( "n",
              Lam
                ( "v1",
                  Lam
                    ( "v2",
                      VecMatch
                        ( Var "v1",
                          Some Nil,
                          Some
                            ( "m",
                              "x",
                              "xs",
                              Cons
                                ( LVar "m",
                                  Pair
                                    ( sv "x",
                                      Syn
                                        (apps (Var "head_bool")
                                           [ sv "m"; sv "v2" ]) ),
                                  Syn
                                    (apps (Var "zip")
                                       [
                                         sv "m";
                                         sv "xs";
                                         Syn
                                           (apps (Var "tail_bool")
                                              [ sv "m"; sv "v2" ]);
                                       ]) ) ) ) ) ) ) );
    typ =
      Pi
        ( "n",
          Nat,
          arrows
            [
              vec Nat (LVar "n");
              vec Bool (LVar "n");
              vec (times Nat Bool) (LVar "n");
            ] );
  }

let test_zip _ = check_program [ head_bool; tail_bool; zip ]

let tests =
  "typecheck"
  >::: [
         "head:ok" >:: test_head;
         "head_bool:ok" >:: test_head_bool;
         "head_vec:ok" >:: test_head_vec;
         "head_abs:ok" >:: test_head_abs;
         "head_poly:ok" >:: test_head_poly;
         "tail:ok" >:: test_tail;
         "tail_bool:ok" >:: test_tail_bool;
         "count_down:ok" >:: test_count_down;
         "count_down:wrong base case" >:: test_count_down_wrong_base_case;
         "count_down:wrong step case" >:: test_count_down_wrong_step_case;
         "count_up:ok" >:: test_count_up;
         "map:ok" >:: test_map;
         "foldl:ok" >:: test_foldl;
         "foldr:ok" >:: test_foldr;
         "zip_with:head and tail:ok" >:: test_zip_with_head_tail;
         "zip_with:nested vmatch:ok" >:: test_zip_with_nested_vmatch;
         "zip_with:0 with 1" >:: test_zip_with_wrong_size_0_vs_1;
         "zip_with:n with m" >:: test_zip_with_wrong_size_n_vs_m;
         "concat:ok" >:: test_concat;
         "reverse:ok" >:: test_reverse_with_concat;
         "take:ok" >:: test_take;
         "take:wrong base case" >:: test_take_wrong_base_case;
         "drop:ok" >:: test_drop;
         "drop:wrong base case" >:: test_drop_wrong_base_case;
         "drop:wrong step case" >:: test_drop_wrong_step_case;
         "dot:ok" >:: test_dot;
         "first_half:ok" >:: test_first_half;
         "vmatch-nil-reachable-missing"
         >:: test_vmatch_nil_case_reachable_but_missing;
         "vmatch-nil-unreachable-implemented"
         >:: test_vmatch_nil_case_unreachable_but_implemented;
         "vmatch-cons-reachable-missing"
         >:: test_vmatch_cons_case_reachable_but_missing;
         "vmatch-cons-unreachable-implemented"
         >:: test_vmatch_cons_case_unreachable_but_implemented;
         "shadowing-at-toplevel" >:: test_shadow_toplevel;
         "shadowing-in-nmatch" >:: test_shadow_in_nmatch;
         "shadowing-in-vmatch" >:: test_shadow_in_vmatch;
         "is_empty:ok" >:: test_is_empty;
         "bool2vec:ok" >:: test_bool2vec;
         "fst_nat:ok" >:: test_fst_nat;
         "snd_nat:ok" >:: test_snd_nat;
         "Nat*Bool:ok" >:: test_nat_bool_pair;
         "dependent-vec-pair:ok" >:: test_dependent_vec_pair;
         "dependent-vec-pair:wrong size" >:: test_dependent_vec_pair_wrong_size;
         "snd:free var" >:: test_snd_free_var;
         "pi-type-wrong-order" >:: test_pi_wrong_order;
         "filter:ok" >:: test_filter;
         "zip:ok" >:: test_zip;
         "mask_filter:ok" >:: test_mask_filter;
       ]

let _ = run_test_tt_main tests
