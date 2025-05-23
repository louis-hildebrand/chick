module StringSet = Set.Make (String)

type str_set = StringSet.t
type len = LVar of string | LNum of int | LSum of len list

type syn_tm = Var of string | App of syn_tm * chk_tm

and chk_tm =
  | Lam of string * chk_tm
  | Fix of string * chk_tm
  | Num of int
  | Sum of chk_tm list
  | Nil
  | Cons of (len (* length of tail *) * chk_tm (* head *) * chk_tm (* tail *))
  | True
  | False
  | Pair of chk_tm * chk_tm
  | Syn of syn_tm
  (* TODO: Need to check that variable names are all distinct? *)
  | VecMatch of
      (syn_tm (* list to match on *)
      * chk_tm option (* expression for the nil case *)
      * (string (* name for length of tail *)
        * string (* name for head of vec *)
        * string (* name for tail of vec *)
        * chk_tm (* expression for the cons case *))
        option)
  | NatMatch of
      (syn_tm (* number to match on *)
      * chk_tm option (* expression for the zero case *)
      * (string (* name for the predecessor *)
        * chk_tm (* expression for the non-zero case *))
        option)
  | BoolMatch of
      (syn_tm (* bool to match on *)
      * chk_tm (* expression for the true case *)
      * chk_tm (* expression for the false case *))
  | PairMatch of
      (* TODO: Need to check that variables names are distinct? *)
      (syn_tm (* pair to match on *)
      * string (* name for fst *)
      * string (* name for snd *)
      * chk_tm (* output *))

type tp =
  | Bool
  | Nat
  | Vec of tp * len
  | Pi of string * tp * tp (* dependent function type (x : A1) -> A2 *)
  | Sigma of string * tp * tp (* dependent pair type (x : A1) * A2 *)

type decl = { name : string; body : chk_tm; typ : tp }
type program = decl list

(** Try to convert an arbitrary expression to a length. *)
let rec len_of_tm (t : chk_tm) : len option =
  match t with
  | Syn (Var x) -> Some (LVar x)
  | Num n -> Some (LNum n)
  | Sum xs ->
      let term_options = List.map len_of_tm xs in
      if List.for_all (fun x -> Option.is_some x) term_options then
        Some (LSum (List.map (fun x -> Option.get x) term_options))
      else None
  | _ -> None

(** Variables in a length. *)
let rec vars (n : len) : str_set =
  match n with
  | LNum _ -> StringSet.empty
  | LVar x -> StringSet.singleton x
  | LSum terms ->
      List.fold_left
        (fun acc x -> StringSet.union acc (vars x))
        StringSet.empty terms

(** Shorthand for a vector type. *)
let vec (tp : tp) (n : len) : tp = Vec (tp, n)

(** Shorthand for the type of a non-dependent function. *)
let arrow (t1 : tp) (t2 : tp) : tp = Pi ("_", t1, t2)

let%test _ = arrow Nat Nat = Pi ("_", Nat, Nat)

(** Shorthand for the type of a non-dependent pair. *)
let times (t1 : tp) (t2 : tp) : tp = Sigma ("_", t1, t2)

let%test _ = times Nat Nat = Sigma ("_", Nat, Nat)

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

(** Convert a length to a string. *)
let rec string_of_len (n : len) : string =
  match n with
  | LNum n -> string_of_int n
  | LVar x -> x
  | LSum terms ->
      let should_parenthesize t =
        match t with LNum _ | LVar _ -> false | _ -> true
      in
      let with_parens t =
        if should_parenthesize t then "(" ^ string_of_len t ^ ")"
        else string_of_len t
      in
      String.concat " + " (List.map with_parens terms)

(** Convert a synthesizable term to a string. *)
let rec string_of_syn_tm (t : syn_tm) : string =
  match t with
  | Var x -> x
  | App (s, t) ->
      let lhs = string_of_syn_tm s in
      let rhs =
        match t with
        | Syn (Var _) | Num _ -> string_of_chk_tm t
        | _ -> "(" ^ string_of_chk_tm t ^ ")"
      in
      lhs ^ " " ^ rhs

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
      let n_str =
        match n with
        | LVar _ | LNum _ -> string_of_len n
        | _ -> "(" ^ string_of_len n ^ ")"
      in
      "cons " ^ n_str ^ " " ^ with_parens x ^ " " ^ with_parens xs
  | True -> "true"
  | False -> "false"
  | Pair (t1, t2) ->
      "(" ^ string_of_chk_tm t1 ^ ", " ^ string_of_chk_tm t2 ^ ")"
  | BoolMatch (s, tt, tf) ->
      "bmatch " ^ string_of_syn_tm s ^ " with | true -> " ^ string_of_chk_tm tt
      ^ " | false -> " ^ string_of_chk_tm tf
  | Syn s -> string_of_syn_tm s
  | NatMatch (s, t0, t1) ->
      let str1 = "nmatch " ^ string_of_syn_tm s ^ " with" in
      let str2 =
        match t0 with
        | None -> str1
        | Some t0 -> str1 ^ " | 0 -> " ^ string_of_chk_tm t0
      in
      let str3 =
        match t1 with
        | None -> str2
        | Some (x, t1) -> str2 ^ " | " ^ x ^ " + 1 -> " ^ string_of_chk_tm t1
      in
      str3
  | VecMatch (s, t0, t1) ->
      let str1 = "vmatch " ^ string_of_syn_tm s ^ " with" in
      let str2 =
        match t0 with
        | None -> str1
        | Some t0 -> str1 ^ " | nil -> " ^ string_of_chk_tm t0
      in
      let str3 =
        match t1 with
        | None -> str2
        | Some (n, x, xs, t1) ->
            str2 ^ " | cons " ^ n ^ " " ^ x ^ " " ^ xs ^ " -> "
            ^ string_of_chk_tm t1
      in
      str3
  | PairMatch (s, x1, x2, t) ->
      "pmatch " ^ string_of_syn_tm s ^ " with | (" ^ x1 ^ ", " ^ x2 ^ ") -> "
      ^ string_of_chk_tm t

let%test _ = string_of_syn_tm (Var "n") = "n"
let%test _ = string_of_syn_tm (App (Var "f", Num 42)) = "f 42"
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
  let actual = string_of_syn_tm (App (Var "f", Sum [ sv "n"; Num 1 ])) in
  let expected = "f (n + 1)" in
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
           Syn (apps (Var "f") [ sv "x"; sv "y" ]);
           Fix ("y", Sum [ sv "y"; sv "y" ]);
         ])
  in
  let expected = "(1 + n) + f x y + (fix y.y + y)" in
  actual = expected

let%test _ =
  let actual =
    string_of_chk_tm
      (Cons
         ( LSum [ LVar "n"; LVar "m" ],
           Sum [ sv "n"; sv "m" ],
           Cons (LVar "j", sv "k", Cons (LNum 0, Num 42, Nil)) ))
  in
  let expected = "cons (n + m) (n + m) (cons j k (cons 0 42 nil))" in
  actual = expected

let%test _ =
  let actual =
    string_of_chk_tm
      (NatMatch (Var "n", Some (Num 42), Some ("m", Sum [ sv "m"; sv "k" ])))
  in
  let expected = "nmatch n with | 0 -> 42 | m + 1 -> m + k" in
  actual = expected

let%test _ =
  let actual =
    string_of_chk_tm
      (VecMatch
         (Var "v", None, Some ("n", "x", "xs", Syn (App (Var "f", sv "x")))))
  in
  let expected = "vmatch v with | cons n x xs -> f x" in
  actual = expected

let%test _ =
  let actual = string_of_chk_tm (VecMatch (Var "v", Some (Num 0), None)) in
  let expected = "vmatch v with | nil -> 0" in
  actual = expected

let%test _ =
  let actual =
    string_of_chk_tm
      (VecMatch (Var "v", Some (Num 0), Some ("n'", "x", "xs", Num 1)))
  in
  let expected = "vmatch v with | nil -> 0 | cons n' x xs -> 1" in
  actual = expected

let%test _ =
  let actual = string_of_chk_tm (BoolMatch (Var "s", False, True)) in
  let expected = "bmatch s with | true -> false | false -> true" in
  actual = expected

let%test _ =
  let actual = string_of_chk_tm (Pair (Num 42, Sum [ sv "x"; sv "y" ])) in
  let expected = "(42, x + y)" in
  actual = expected

let%test _ =
  let actual =
    string_of_chk_tm (PairMatch (Var "p", "y1", "y2", Sum [ sv "y1"; sv "y2" ]))
  in
  let expected = "pmatch p with | (y1, y2) -> y1 + y2" in
  actual = expected

(** Convert a type to a string. *)
let rec string_of_tp (t : tp) : string =
  match t with
  | Nat -> "Nat"
  | Bool -> "Bool"
  | Vec (tp, n) ->
      let should_parenthesize_tp =
        match tp with Nat | Bool -> false | _ -> true
      in
      let should_parenthesize_len =
        match n with LNum _ | LVar _ -> false | _ -> true
      in
      let tp_str =
        if should_parenthesize_tp then "(" ^ string_of_tp tp ^ ")"
        else string_of_tp tp
      in
      let s =
        if should_parenthesize_len then "(" ^ string_of_len n ^ ")"
        else string_of_len n
      in
      "Vec " ^ tp_str ^ " " ^ s
  | Pi (x, t1, t2) ->
      "Pi (" ^ x ^ ":" ^ string_of_tp t1 ^ ") . " ^ string_of_tp t2
  | Sigma (x, t1, t2) ->
      "Sigma (" ^ x ^ ":" ^ string_of_tp t1 ^ ") . " ^ string_of_tp t2

let%test _ = string_of_tp Nat = "Nat"
let%test _ = string_of_tp (vec Nat (LNum 0)) = "Vec Nat 0"
let%test _ = string_of_tp (Vec (Bool, LVar "n")) = "Vec Bool n"

let%test _ =
  string_of_tp (Vec (Vec (Nat, LVar "n"), LVar "n")) = "Vec (Vec Nat n) n"

let%test _ =
  string_of_tp (Vec (Nat, LSum [ LVar "n"; LVar "m" ])) = "Vec Nat (n + m)"

let%test _ =
  string_of_tp (Pi ("n", Nat, Vec (Nat, LVar "n"))) = "Pi (n:Nat) . Vec Nat n"

let%test _ =
  let actual = string_of_tp (arrow (times Nat Nat) Nat) in
  let expected = "Pi (_:Sigma (_:Nat) . Nat) . Nat" in
  actual = expected

let%test _ =
  string_of_tp (Sigma ("n", Nat, vec Bool (LVar "n")))
  = "Sigma (n:Nat) . Vec Bool n"
