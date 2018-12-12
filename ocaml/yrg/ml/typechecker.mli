open Syntax

(** [check t] traverses the typing derivation [t] to check if it is
    well-formed...*)
val check : Syntax.XTerm.t -> Syntax.XTerm.t

(** ... if not, one of the following exceptions is raised: *)
exception IllformedType of Name.t list * Type.t
exception InvalidInstance of Name.t * TypeScheme.t * Type.t
exception IncompatibleTypes of Type.t * Type.t
exception IncompatibleTypeSchemes of TypeScheme.t * TypeScheme.t
exception OnlyFunctionCanBeApplied

(** [string_of_error error] returns a human-readable representation
    of the previous [error]s. *)
val string_of_error : exn -> string
