open Syntax

(** [mgu ty1 ty2] returns [phi] such that [phi ty1 = phi ty2] and
    [phi] is the most general substitution which entails this equality.
    In case of error, [mgu] raises [IncompatiblesType (ty1, ty2)]
    or [CyclicType (x, ty)] if the problem only admits cyclic
    answers. *)
val mgu : Type.t -> Type.t -> Type.t Substitution.t

exception CyclicType of Syntax.Name.t * Syntax.Type.t

exception IncompatibleTypes of Syntax.Type.t * Syntax.Type.t

(** [string_of_error error] returns a human readable representation of
    two previous [error]s. *)
val string_of_error : exn -> string
