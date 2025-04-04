type equation
(** An equality between lengths. *)

val always_equal : equation -> equation list -> bool
(** Check whether, with the given assumptions, the given lengths are equal. All
    variables are universally quantified. *)

val can_equal : equation -> equation list -> bool
(** Check whether, with the given assumptions, the given lengths can be made
    equal. All variables are existentially quantified. *)
