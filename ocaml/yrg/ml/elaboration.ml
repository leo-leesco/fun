open Syntax
open Mgu

module I = ITerm
module X = XTerm

let substitute_env phi = Env.map (TypeScheme.substitute phi)

let generalized_variables (ty_env : TypeScheme.t Env.t) ty : Name.t list =
  Env.fold
    (fun xs _ s -> NameSet.diff xs (TypeScheme.free_type_variables s))
    (Type.free_type_variables ty)
    ty_env
  |> NameSet.elements

let algorithm_w (ast : I.t) : X.t =
  failwith "Student! This is your job!"

let type_error program e =
  Printf.printf
    "Type error during type inference because %s.\n"
    (Mgu.string_of_error e);
  exit 1

let elaborate : Syntax.ITerm.t -> Syntax.XTerm.t = fun program ->
  try
    algorithm_w program
  with e ->
    type_error program e
