open Syntax

exception CyclicType of Name.t * Type.t
exception IncompatibleTypes of Type.t * Type.t

let string_of_error = function
  | CyclicType (v, ty) ->
     Printf.sprintf
       "the equation %s = %s cannot be solved"
       (Name.string_of_name v)
       (Type.string_of_type ty)
  | IncompatibleTypes (ty1, ty2) ->
     Printf.sprintf
       "the types %s and %s are incompatible"
       (Type.string_of_type ty1)
       (Type.string_of_type ty2)
  | e ->
     Printexc.to_string e

let compose =
  Substitution.compose (fun x ty -> Type.(equal (var x) ty)) Type.substitute

let mgu ty1 ty2 = Type.(
    let substitute_all x ty c =
      let phi = Substitution.(binding x ty) in
      List.map (fun (ty1, ty2) -> (substitute phi ty1, substitute phi ty2)) c
    in

    let rec aux = function
      | [] ->
         Substitution.identity
      | (Var y, Var x) :: c when Name.compare x y = 0 ->
         aux c
      | ((Var x, ty) | (ty, Var x)) :: c ->
         if NameSet.mem x (Type.free_type_variables ty) then
           raise (CyclicType (x, ty))
         else
           compose (aux (substitute_all x ty c)) (Substitution.binding x ty)
      | ((App (tycon1, tys1) as ty1), (App (tycon2, tys2) as ty2)) :: c ->
         if not (TypeConstructor.equal tycon1 tycon2) then
           raise (IncompatibleTypes (ty1, ty2))
         else
           aux (List.combine tys1 tys2 @ c)
    in
    let phi = aux [(ty1, ty2)] in
    if !Options.debug then
      Printf.printf "MGU(%s, %s) = %s\n"
        (Type.string_of_type ty1)
        (Type.string_of_type ty2)
        (Substitution.string_of_substitution Type.string_of_type phi);
    phi
  )

let instance_of s ty' =
  let xs, ty = TypeScheme.instance s in
  let phi = mgu ty ty' in
  List.for_all
    (fun x -> List.exists (fun y -> Name.compare x y = 0) xs)
    (Substitution.domain phi)
