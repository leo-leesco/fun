open Syntax

module S = struct

  type 'a structure =
    | TyApp of TypeConstructor.t * 'a list

  let rec map f (TyApp (t, ts)) = TyApp (t, List.map f ts)

  let fold f (TyApp (_, ts)) accu = List.fold_right f ts accu

  let iter f (TyApp (_, ts)) = List.iter f ts

  exception Iter2

  let rec iter2 f (TyApp (t, ts)) (TyApp (u, us)) =
    if TypeConstructor.equal u t then List.iter2 f ts us else raise Iter2

end

module O = struct

  type tyvar =
    int

  type 'a structure =
    'a S.structure

  type ty =
    Type.t

  let mangle =
    let t = Hashtbl.create 13 in
    fun x ->
    try Hashtbl.find t x with
    | Not_found ->
       let y = Name.fresh (Printf.sprintf "'a_%d") in
       Hashtbl.add t x y;
       y

  let variable =
    fun x -> Type.var (mangle x)

  let structure (S.TyApp (t, ts)) =
    Type.app t ts

  let mu x t =
    failwith "No recursive types"

  type scheme =
    tyvar list * ty

end

module Solver =
  Inferno.SolverHi.Make(struct include Name type tevar = t end)(S)(O)

let arrow a b = S.TyApp (TypeConstructor.arrow, [a; b])

let int_type = S.TyApp (TypeConstructor.int, [])

module I = ITerm
module X = XTerm

let generate_constraint : ITerm.t -> XTerm.t Solver.co =
  fun t ->
  failwith "Students! This is your job!"

let elaborate : ITerm.t -> XTerm.t =
  fun t ->
  let program_constraint = generate_constraint t in
  let global_constraint = Solver.let0 program_constraint in
  snd (Solver.solve false global_constraint)
