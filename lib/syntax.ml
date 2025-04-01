type syn_tm =
  | Var of string
  | App of syn_tm * chk_tm
  (* TODO: It would be nice to remove these and implement them using VecMatch.
           This would require supporting matching vectors whose length is NOT a
           simple variable, but that should be doable. *)
  | Head of (chk_tm (* length of tail *) * syn_tm (* vector *))
  | Tail of (chk_tm (* length of tail *) * syn_tm (* vector *))

and chk_tm =
  | Lam of string * chk_tm
  | Fix of string * chk_tm
  | Num of int
  | Sum of chk_tm list
  | Nil
  | Cons of
      (chk_tm (* length of tail *) * chk_tm (* head *) * chk_tm (* tail *))
  | Syn of syn_tm
  | VecMatch of
      (syn_tm (* list to match on *)
      * chk_tm (* expression for the nil case *)
      * string (* name for length of tail *)
      * string (* name for head of vec *)
      * string (* name for tail of vec *)
      * chk_tm (* expression for the cons case *))
  | NatMatch of
      (syn_tm (* number to match on *)
      * chk_tm (* expression for the zero case *)
      * string (* expression for the predecessor *)
      * chk_tm (* expression for the non-zero case *))

type tp = Nat | Vec of chk_tm | Pi of string * tp * tp
type kind = KTp | KPi of string * tp * kind
type decl = { name : string; body : chk_tm; typ : tp }
type program = decl list

(** Shorthand for the type of a non-dependent function. *)
let arrow (t1 : tp) (t2 : tp) : tp = Pi ("_", t1, t2)

let%test _ = arrow Nat Nat = Pi ("_", Nat, Nat)

(** Shorthand for a chain of arrows. *)
let rec arrows (ts : tp list) : tp =
  match ts with
  | [] | [ _ ] -> raise (Invalid_argument "Not enough arguments")
  | [ t1; t2 ] -> arrow t1 t2
  | t :: ts -> arrow t (arrows ts)

let%test _ = arrows [ Nat; Nat ] = Pi ("_", Nat, Nat)
let%test _ = arrows [ Nat; Nat; Nat ] = Pi ("_", Nat, Pi ("_", Nat, Nat))

let%test _ =
  arrows [ Nat; Nat; Nat; Nat ]
  = Pi ("_", Nat, Pi ("_", Nat, Pi ("_", Nat, Nat)))

(** Shorthand for applying a function to many arguments. *)
let apps (f : syn_tm) (args : chk_tm list) : syn_tm =
  List.fold_left (fun f a -> App (f, a)) f args

(** Shorthand for a variable as a checkable term. *)
let sv (name : string) : chk_tm = Syn (Var name)

(** Convert a synthesizable term to a string. *)
let rec string_of_syn_tm (t : syn_tm) : string =
  match t with
  | Var x -> x
  | App (s, t) ->
      let lhs =
        match s with
        | Var f -> f
        | App _ -> string_of_syn_tm s
        | _ -> "(" ^ string_of_syn_tm s ^ ")"
      in
      let rhs =
        match t with Syn (Var x) -> x | _ -> "(" ^ string_of_chk_tm t ^ ")"
      in
      lhs ^ " " ^ rhs
  | Head (t, s) ->
      let t_str =
        match t with
        | Num _ | Syn (Var _) -> string_of_chk_tm t
        | _ -> "(" ^ string_of_chk_tm t ^ ")"
      in
      let s_str =
        match s with
        | Var _ -> string_of_syn_tm s
        | _ -> "(" ^ string_of_syn_tm s ^ ")"
      in
      "head " ^ t_str ^ " " ^ s_str
  | Tail (t, s) ->
      let t_str =
        match t with
        | Num _ | Syn (Var _) -> string_of_chk_tm t
        | _ -> "(" ^ string_of_chk_tm t ^ ")"
      in
      let s_str =
        match s with
        | Var _ -> string_of_syn_tm s
        | _ -> "(" ^ string_of_syn_tm s ^ ")"
      in
      "tail " ^ t_str ^ " " ^ s_str

(** Convert a checkable term to a string. *)
and string_of_chk_tm (t : chk_tm) : string =
  match t with
  | Lam (x, t) -> "\\" ^ x ^ "." ^ string_of_chk_tm t
  | Fix (x, t) -> "fix " ^ x ^ "." ^ string_of_chk_tm t
  | Num n -> string_of_int n
  | Sum ts ->
      let should_parenthesize t =
        match t with Syn _ | Num _ -> false | _ -> true
      in
      let with_parens t =
        if should_parenthesize t then "(" ^ string_of_chk_tm t ^ ")"
        else string_of_chk_tm t
      in
      String.concat " + " (List.map with_parens ts)
  | Nil -> "nil"
  | Cons (n, x, xs) ->
      let should_parenthesize t =
        match t with Num _ | Syn (Var _) | Nil -> false | _ -> true
      in
      let with_parens t =
        if should_parenthesize t then "(" ^ string_of_chk_tm t ^ ")"
        else string_of_chk_tm t
      in
      "cons " ^ with_parens n ^ " " ^ with_parens x ^ " " ^ with_parens xs
  | Syn s -> string_of_syn_tm s
  | NatMatch (s, t0, x, t1) ->
      "nmatch " ^ string_of_syn_tm s ^ " with | 0 -> " ^ string_of_chk_tm t0
      ^ " | " ^ x ^ " + 1 -> " ^ string_of_chk_tm t1
  | VecMatch (s, t0, n, x, xs, t1) ->
      "vmatch " ^ string_of_syn_tm s ^ " with | nil -> " ^ string_of_chk_tm t0
      ^ " | cons " ^ n ^ " " ^ x ^ " " ^ xs ^ " -> " ^ string_of_chk_tm t1

let%test _ = string_of_syn_tm (Var "n") = "n"
let%test _ = string_of_syn_tm (App (Var "f", sv "x")) = "f x"

let%test _ =
  let actual = string_of_syn_tm (App (App (Var "f", sv "x"), sv "y")) in
  let expected = "f x y" in
  actual = expected

let%test _ =
  let actual = string_of_syn_tm (App (Var "f", Syn (App (Var "g", sv "x")))) in
  let expected = "f (g x)" in
  actual = expected

let%test _ =
  let actual = string_of_syn_tm (Head (sv "n", Var "v")) in
  let expected = "head n v" in
  actual = expected

let%test _ =
  let actual =
    string_of_syn_tm (Head (Sum [ sv "n"; sv "m" ], App (Var "f", sv "x")))
  in
  let expected = "head (n + m) (f x)" in
  actual = expected

let%test _ =
  let actual = string_of_syn_tm (Tail (sv "n", Var "v")) in
  let expected = "tail n v" in
  actual = expected

let%test _ =
  let actual =
    string_of_syn_tm (Tail (Sum [ sv "n"; sv "m" ], App (Var "f", sv "x")))
  in
  let expected = "tail (n + m) (f x)" in
  actual = expected

let%test _ =
  let actual = string_of_chk_tm (Lam ("x", Syn (App (Var "f", sv "x")))) in
  let expected = "\\x.f x" in
  actual = expected

let%test _ =
  let actual = string_of_chk_tm (Fix ("x", Syn (App (Var "f", sv "x")))) in
  let expected = "fix x.f x" in
  actual = expected

let%test _ =
  let actual =
    string_of_chk_tm
      (Sum
         [
           Sum [ Num 1; sv "n" ];
           Syn (Head (sv "n", Var "v"));
           Syn (App (Var "f", sv "x"));
           Fix ("y", Sum [ sv "y"; sv "y" ]);
         ])
  in
  let expected = "(1 + n) + head n v + f x + (fix y.y + y)" in
  actual = expected

let%test _ =
  let actual =
    string_of_chk_tm
      (Cons
         ( Sum [ sv "n"; sv "m" ],
           Sum [ sv "n"; sv "m" ],
           Cons (sv "j", sv "k", Cons (Num 0, Num 42, Nil)) ))
  in
  let expected = "cons (n + m) (n + m) (cons j k (cons 0 42 nil))" in
  actual = expected

let%test _ =
  let actual =
    string_of_chk_tm (NatMatch (Var "n", Num 42, "m", Sum [ sv "m"; sv "k" ]))
  in
  let expected = "nmatch n with | 0 -> 42 | m + 1 -> m + k" in
  actual = expected

let%test _ =
  let actual =
    string_of_chk_tm
      (VecMatch (Var "v", Nil, "n", "x", "xs", Syn (App (Var "f", sv "x"))))
  in
  let expected = "vmatch v with | nil -> nil | cons n x xs -> f x" in
  actual = expected

(** Convert a type to a string. *)
let rec string_of_tp (t : tp) : string =
  match t with
  | Nat -> "Nat"
  | Vec n ->
      let n_str =
        match n with
        | Num n -> string_of_int n
        | Syn (Var n) -> n
        | _ -> "(" ^ string_of_chk_tm n ^ ")"
      in
      "Vec " ^ n_str
  | Pi (x, t1, t2) ->
      "Pi (" ^ x ^ ":" ^ string_of_tp t1 ^ ") . " ^ string_of_tp t2

let%test _ = string_of_tp Nat = "Nat"
let%test _ = string_of_tp (Vec (Num 0)) = "Vec 0"
let%test _ = string_of_tp (Vec (sv "n")) = "Vec n"
let%test _ = string_of_tp (Vec (Sum [ sv "n"; sv "m" ])) = "Vec (n + m)"
let%test _ = string_of_tp (Pi ("n", Nat, Vec (sv "n"))) = "Pi (n:Nat) . Vec n"
