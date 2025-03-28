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
