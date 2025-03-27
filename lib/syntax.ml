type syn_tm = Var of string | App of syn_tm * chk_tm

and chk_tm =
  | Lam of string * chk_tm
  | Fix of string * chk_tm
  | Num of int
  | Sum of chk_tm list
  | Nil
  | Cons of chk_tm * chk_tm
  | Syn of syn_tm
  | Case of
      (syn_tm (* list to match on *)
      * chk_tm (* expression for the nil case *)
      * string (* name for head of vec *)
      * string (* name for tail of vec *)
      * chk_tm (* expression for the cons case *))

type tp = Nat | Vec of chk_tm | Pi of string * tp * tp
type kind = KTp | KPi of string * tp * kind
type decl = { name : string; body : chk_tm; typ : tp }
type program = decl list
