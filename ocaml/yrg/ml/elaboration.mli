(** [elaborate t] turns an implicitly typed program into an explicitly
    typed one. *)
val elaborate : Syntax.ITerm.t -> Syntax.XTerm.t
