open Syntax
open Mgu

module X = Syntax.XTerm

exception IllformedType of Name.t list * Type.t
exception InvalidInstance of Name.t * TypeScheme.t * Type.t
exception IncompatibleTypes of Type.t * Type.t
exception IncompatibleTypeSchemes of TypeScheme.t * TypeScheme.t
exception OnlyFunctionCanBeApplied

let string_of_error = function
  | IllformedType (vs, ty) ->
     Printf.sprintf
       "The type %s is not well-formed. Only [%s] are in scope"
       (Type.string_of_type ty)
       (String.concat " " (List.map Name.string_of_name vs))
  | InvalidInstance (x, s, ty) ->
     Printf.sprintf
       "%s has type %s, which is not an instance of %s"
       (Name.string_of_name x)
       (TypeScheme.string_of_type_scheme s)
       (Type.string_of_type ty)
  | IncompatibleTypes (ty1, ty2) ->
     Printf.sprintf
       "Types %s and %s are incompatible"
       (Type.string_of_type ty1)
       (Type.string_of_type ty2)
  | IncompatibleTypeSchemes (s1, s2) ->
     Printf.sprintf
       "Type scheme %s and %s are incompatible."
       (TypeScheme.string_of_type_scheme s1)
       (TypeScheme.string_of_type_scheme s2)
  | OnlyFunctionCanBeApplied ->
     Printf.sprintf "Only functions can be applied"
  | e ->
     Printexc.to_string e

let wf_type vs ty =
  if NameSet.(diff (Type.free_type_variables ty) vs <> empty) then (
    raise (IllformedType (NameSet.elements vs, ty)))

let bind_type_variables xs vs =
  List.fold_right NameSet.add xs vs

let check (program : X.t) =
  failwith "Student! This is your job!"

let type_error program e =
  Printf.printf
    "The following program is ill-typed:\n%s\nbecause %s.\n"
    (XTerm.string_of_xterm program)
    (string_of_error e);
  exit 1

let check program = try
    check program
  with e ->
    type_error program e
