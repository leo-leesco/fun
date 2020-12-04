(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-27-32-33-37-39-60"]

(* -------------------------------------------------------------------------- *)

(* We use the following term variables. *)

module T = struct

  type tevar = string

  let compare = String.compare

end

(* -------------------------------------------------------------------------- *)

(* We use the following type algebra. *)

(* Our types are divided into three sorts:

   - a sort [TYPE] of ordinary types,
   - a sort [LIST] of lists of arguments,
   - a sort [ARGM] of arguments.

   The axioms of the sort discipline are as follows:

     Bool   : TYPE
     String : TYPE
     Arrow  : LIST -> TYPE -> TYPE
     Nil    : LIST
     Cons   : ARGM -> LIST -> LIST
     Value  : TYPE -> ARGM
     Block  : TYPE -> ARGM

  The fact that every type is well-sorted should be true by construction,
  but it is up to you to respect this discipline.

  In the constraint generation code, we write [typev], [listv], and [argmv]
  for type variables whose sort is [TYPE], [LIST], and [ARGM], respectively. *)

module S = struct

  type constructor =
    | Bool   (* arity 0 *)
    | String (* arity 0 *)
    | Arrow  (* arity 2 *)
    | Nil    (* arity 0 *)
    | Cons   (* arity 2 *)
    | Value  (* arity 1 *)
    | Block  (* arity 1 *)

  type 'a structure =
    constructor * 'a list
      (* The length of the list is the arity of the constructor *)

  let map f (c, args) =
    (c, List.map f args)

  let fold f (_, args) accu =
    List.fold_right f args accu

  let iter f (_, args) =
    List.iter f args

  exception Iter2

  let iter2 f (c1, args1) (c2, args2) =
    if c1 = c2 then
      List.iter2 f args1 args2
    else
      raise Iter2

end

let bool =
  (S.Bool, [])

let string =
  (S.String, [])

let arrow x y =
  (S.Arrow, [x; y])

let nil =
  (S.Nil, [])

let cons x y =
  (S.Cons, [x; y])

let value x =
  (S.Value, [x])

let blokk x =
  (S.Block, [x])

(* -------------------------------------------------------------------------- *)

(* The syntax of decoded types is as follows. It is used when a type error
   message is printed. *)

module O = struct
  type tyvar = int
  let solver_tyvar v = v
  type 'a structure = 'a S.structure
  type ty =
    | TyVar of tyvar
    | TyCon of ty structure
    | TyMu of tyvar * ty
  let variable v = TyVar v
  let structure s = TyCon s
  let mu v ty = TyMu (v, ty)
  type scheme = tyvar list * ty
end

(* -------------------------------------------------------------------------- *)

(* A pretty-printer of decoded types. *)

module P = struct

  open PPrint
  open S
  open O

  let atom =
    string

  let arrow =
    atom " ->" ^^ break 1

  let cons =
    atom " ::" ^^ break 1

  let mu =
    atom "mu "

  let dot =
    atom " ." ^^ break 1

  let print_tyvar v =
    utf8format "'a%d" v

  (* We adopt the convention that [cons] binds tighter than [arrow]. We need
     three priority levels: at level 0, no lists or arrows or mus are allowed;
     at level 1, lists are allowed, but not arrows or mus; at level 2, all
     constructs are allowed. *)

  let rec print_ty ty =
    print_ty_2 ty

  and print_ty_2 ty =
    match ty with
    | TyCon (Arrow, [ty1; ty2]) ->
        group (print_ty_1 ty1 ^^ arrow ^^ print_ty_2 ty2)
    | TyCon (Arrow, _) ->
        assert false (* internal arity error; cannot happen *)
    | TyMu (v, ty) ->
        mu ^^ print_tyvar v ^^ dot ^^ print_ty_2 ty
    | _ ->
        print_ty_1 ty

  and print_ty_1 ty =
    match ty with
    | TyCon (Cons, [ty1; ty2]) ->
        group (print_ty_0 ty1 ^^ cons ^^ print_ty_1 ty2)
    | TyCon (Cons, _) ->
        assert false (* internal arity error; cannot happen *)
    | _ ->
        print_ty_0 ty

  and print_ty_0 ty =
    match ty with
    | TyVar v ->
        print_tyvar v
    | TyCon (Bool, tys) ->
        assert (tys = []); (* internal arity check *)
        atom "bool"
    | TyCon (String, tys) ->
        assert (tys = []); (* internal arity check *)
        atom "string"
    | TyCon (Nil, tys) ->
        assert (tys = []); (* internal arity check *)
        atom "[]"
    | TyCon (Value, [ty]) ->
        atom "value " ^^ print_ty_0 ty
    | TyCon (Value, _) ->
        assert false (* internal arity error; cannot happen *)
    | TyCon (Block, [ty]) ->
        atom "block " ^^ print_ty_0 ty
    | TyCon (Block, _) ->
        assert false (* internal arity error; cannot happen *)
    | _ ->
        group (nest 2 (lparen ^^ break 0 ^^ print_ty ty) ^^ break 0 ^^ rparen)

  let render (doc : document) : string =
    let b = Buffer.create 128 in
    PPrint.ToBuffer.pretty 0.8 78 b doc;
    Buffer.contents b

  let print_ty ty =
    render (group (print_ty ty))

end

let print_ty =
  P.print_ty

(* -------------------------------------------------------------------------- *)

(* We instantiate Inferno's constraint solver as follows. *)

include Inferno.SolverHi.Make(T)(S)(O)

(* -------------------------------------------------------------------------- *)

(* Inferno's [build] combinator takes a deep type as an argument. It can be
   useful when generating constraints; without it, one would need to manually
   decompose a deep type into a bunch of type variables and shallow types. *)

(* The function [Deep.arrow] helps build a (deep) arrow type. *)

module Deep = struct

  open S

  let var x =
    DeepVar x

  (* [list] expects a list of structures of sort [ARGM] and produces a deep
     type of sort [LIST]. *)

  let rec list (ss : variable structure list) : deep_ty =
    match ss with
    | [] ->
        DeepStructure nil
    | s :: ss ->
        DeepStructure (cons (DeepStructure (S.map var s)) (list ss))

  (* [arrow] expects a list [ss] of structures of sort [ARGM] and a type
     variable of sort [TYPE] and produces a deep type of sort [TYPE]. *)

  let arrow (ss : variable structure list) (w : variable) : deep_ty =
    DeepStructure (arrow (list ss) (DeepVar w))

end

(* -------------------------------------------------------------------------- *)

(* Constraint construction. *)

(* We perform monomorphic type inference; there is no polymorphism. We produce
   unification constraints only. *)

(* We do not construct an explicitly-typed program. If the solver succeeds,
   then the result is a unit value. For this reason, our constraints have
   type [unit co]. *)

(* We exploit the fact that value variables [x] and block variables [F] have
   distinct names. This allows us to insert them together in an environment
   without risk of confusion. *)

open SystemXi

(* [statement s typev] expresses the fact that [s] has type [typev]. *)

let rec statement (s : statement) (typev : variable) : unit co =
  pure ()
  (* TASK: implement this function. *)
(* -------------------------------------------------------------------------- *)

(* Constraint solving. *)

(* Run the solver and catch its exceptions. *)

open Printf

let explain e =
  match e with
  | Unbound (_, x) ->
      eprintf
        "The variable \"%s\" is unbound.\n" x
  | Unify (_, ty1, ty2) ->
      eprintf
        "The following types cannot be unified:\n%s\n%s\n"
        (print_ty ty1) (print_ty ty2)
  | Cycle (_, ty) ->
      eprintf
        "The following type is cyclic:\n%s\n"
        (print_ty ty)
  | _ ->
      assert false

let typecheck (s : statement) =
  try
    solve false (
      let0 (exist_ @@ fun typev -> statement s typev)
    )
    |> ignore
  with (Unbound (range, _) | Unify (range, _, _) | Cycle (range, _)) as e ->
    printf "TYPE ERROR\n";
    LexerUtil.print_range stderr range;
    explain e;
    exit 0
