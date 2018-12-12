(** The type of environments that map names to values of type ['a]. *)
type 'a t

(** The [empty] environment. *)
val empty : 'a t

(** [bind x v env] extends [env] with a new binding from [x] to [v]. *)
val bind : Syntax.Name.t -> 'a -> 'a t -> 'a t

(** [lookup x env] returns the image of [x] by [env] if it exists. *)
val lookup : Syntax.Name.t -> 'a t -> 'a

(** [UnboundIdentifier x] is raised if [lookup x env] fails. *)
exception UnboundIdentifier of Syntax.Name.t

val fold : ('b -> Syntax.Name.t -> 'a -> 'b) -> 'b -> 'a t -> 'b

val map : ('a -> 'b) -> 'a t -> 'b t
