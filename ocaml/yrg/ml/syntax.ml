(**

    A (naive) purely functional implementation of Hindley Milner type
    system and type inference.

 *)

(** {1 Misc.} *)
module Printer : sig
  val parenthesize : string -> string
  val parenthesize_if : bool -> string -> string
  val separated : string -> string list -> string
end = struct
  let parenthesize s = "(" ^ s ^ ")"
  let parenthesize_if b s = if b then parenthesize s else s
  let separated = String.concat
end

(** {1  Names} *)

module Name : sig
  type t
  val make    : (int -> string) -> t
  val fresh   : (int -> string) -> t
  val refresh : t -> t
  val compare : t -> t -> int
  val string_of_name : t -> string
  val in_list : t -> t list -> bool
end = struct
  type t = { show : int -> string; salt : int }
  let count = ref 0
  let salt () = incr count; !count
  let make show = { show; salt = 0 }
  let fresh show = { show; salt = salt () }
  let refresh { show } = fresh show
  let string_of_name { show; salt } = show salt
  let compare n1 n2 = String.compare (string_of_name n1) (string_of_name n2)
  let in_list x ys = List.exists (fun y -> compare y x = 0) ys
end

module NameSet = Set.Make (Name)

(** {1 Implicitly-typed terms} *)

module ITerm : sig
  type t =
    | Var of Name.t
    | App of t * t
    | Lam of Name.t * t
    | Let of Name.t * t * t
    | Lit of int
end = struct
  type t =
    | Var of Name.t
    | App of t * t
    | Lam of Name.t * t
    | Let of Name.t * t * t
    | Lit of int
end

(** {1 Substitution} *)
module Substitution : sig
  type 'a t
  val identity : 'a t
  val binding : Name.t -> 'a -> 'a t
  val compose
      : (Name.t -> 'a -> bool) -> ('a t -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val disjoint_union : 'a t -> 'a t -> 'a t
  val get : 'a t -> Name.t -> 'a option
  val map : ('a -> 'b) -> 'a t -> 'b t
  val domain : 'a t -> Name.t list
  val string_of_substitution : ('a -> string) -> 'a t -> string
end = struct
  type 'a t = (Name.t * 'a) list
  let identity = []
  let binding x v = [(x, v)]
  let get (m : 'a t) x =
    let rec aux = function
      | [] -> None
      | (y, v) :: vs -> if Name.compare x y = 0 then Some v else aux vs
    in
    aux m
  let map f = List.map (fun (x, v) -> (x, f v))
  let domain phi = fst (List.split phi)
  let in_domain x phi = List.exists (fun y -> Name.compare x y = 0) (domain phi)
  let compose trivial subst m2 m1 =
    List.map (fun (x, v) -> (x, subst m2 v)) m1
    @ List.filter (fun (x, _) -> not (in_domain x m1)) m2
    |> List.filter (fun (x, v) -> not (trivial x v))
  let disjoint_union = ( @ )
  let string_of_substitution print phi =
    let string_of_binding (x, v) =
      Printf.sprintf "%s ↦ %s" (Name.string_of_name x) (print v)
    in
    Printf.sprintf "[%s]" (String.concat "; " (List.map string_of_binding phi))
end

(** {1 Type algebra} *)

module TypeConstructor : sig
  type t
  val arity : t -> int
  val equal : t -> t -> bool
  val make_type_constructor : string -> int -> t
  val string_of_type_constructor : t -> string
  val arrow : t
  val int : t
end = struct
  type t = string * int
  let arity = snd
  let equal = ( = )
  let make_type_constructor x a = (x, a)
  let string_of_type_constructor = fst
  let arrow = ("->", 2)
  let int = ("int", 0)
end

module Type : sig
  type t = private
    | Var of Name.t
    | App of TypeConstructor.t * t list

  val equal : t -> t -> bool

  val var : Name.t -> t

  exception InvalidArity of TypeConstructor.t * int * int

  val app : TypeConstructor.t -> t list -> t

  val arrow : t -> t -> t

  val int : t

  val destruct_arrow : t -> (t * t) option

  val equal : t -> t -> bool

  val substitute : t Substitution.t -> t -> t

  val refresh : Name.t Substitution.t -> t -> t

  val fresh_variable : unit -> Name.t

  val free_type_variables : t -> NameSet.t

  val string_of_type : t -> string

end = struct
  type t =
    | Var of Name.t
    | App of TypeConstructor.t * t list

  let rec equal ty1 ty2 =
    match ty1, ty2 with
    | Var x, Var y ->
       Name.compare x y = 0
    | App (tc1, tys1), App (tc2, tys2) ->
       List.(length tys1 = length tys2)
       && TypeConstructor.equal tc1 tc2
       && List.for_all2 equal tys1 tys2
    | _, _ ->
       false

  let var x = Var x

  let fresh_variable () = Name.fresh (fun i ->
     "'"
     ^ if i >= 0 && i <= 25 then
       String.make 1 (Char.chr (97 + i))
     else
       Printf.sprintf "'a[%d]" i
  )

  let rec equal t1 t2 =
    match t1, t2 with
    | Var x, Var y ->
       Name.compare x y = 0
    | App (tycon1, tys1), App (tycon2, tys2) ->
       TypeConstructor.equal tycon1 tycon2 && List.for_all2 equal tys1 tys2
    | _, _ ->
       false

  exception InvalidArity of TypeConstructor.t * int * int

  let app tycon tys =
    let ntys = List.length tys and atycon = TypeConstructor.arity tycon in
    if ntys <> atycon then raise (InvalidArity (tycon, atycon, ntys));
    App (tycon, tys)

  let arrow in_ty out_ty =
    app TypeConstructor.arrow [in_ty; out_ty]

  let int =
    app TypeConstructor.int []

  let destruct_arrow = function
    | App (tycon, [ty1; ty2]) when TypeConstructor.(equal tycon arrow) ->
       Some (ty1, ty2)
    | _ ->
       None

  let rec substitute phi = function
    | App (tycon, tys) ->
       App (tycon, List.map (substitute phi) tys)
    | Var x -> match Substitution.get phi x with
               | None -> Var x
               | Some t -> t

  let refresh phi = substitute (Substitution.map (fun x -> Var x) phi)

  let rec string_of_type = Printer.(function
    | Var x ->
       Name.string_of_name x
    | App (tycon, tys) as t ->
       match destruct_arrow t with
       | Some (ty1, ty2) ->
          parenthesize_if (destruct_arrow ty1 <> None) (string_of_type ty1)
          ^ " -> "
          ^ string_of_type ty2
       | None ->
          TypeConstructor.string_of_type_constructor tycon
          ^ parenthesize (separated ", " (List.map string_of_type tys))
  )

  let rec free_type_variables = NameSet.(function
    | Var x ->
       singleton x
    | App (_, tys) ->
       List.fold_left union empty (List.map free_type_variables tys))

end

module TypeScheme : sig
  type t = private Forall of Name.t list * Type.t
  val forall : Name.t list -> Type.t -> t
  val equivalent : t -> t -> bool
  val instance : t -> Name.t list * Type.t
  val substitute : Type.t Substitution.t -> t -> t
  val free_type_variables : t -> NameSet.t
  val string_of_type_scheme : t -> string
end = struct
  type t = Forall of Name.t list * Type.t

  let renaming xs xs' =
    let bind m x v = Substitution.(disjoint_union m (binding x v)) in
    Substitution.(List.fold_left2 bind identity xs xs')

  let forall xs ty =
    let rec aux ss = function
      | Type.Var x ->
         if Name.in_list x ss then ss
         else if Name.in_list x xs then x :: ss
         else ss
      | Type.App (_, tys) ->
         List.fold_left aux ss tys
    in
    let xs = aux [] ty in
    let xs' = List.map Name.refresh xs in
    Forall (xs', Type.refresh (renaming xs xs') ty)

  let free_type_variables (Forall (xs, ty)) =
    List.fold_left
      (fun s x -> NameSet.remove x s)
      (Type.free_type_variables ty)
      xs

  let unbox (Forall (xs, ty)) = (xs, ty)

  let equivalent (Forall (xs1, ty1)) (Forall (xs2, ty2)) =
    let xs = List.map Name.refresh xs1 in
    Type.(equal (refresh (renaming xs1 xs) ty1) (refresh (renaming xs2 xs) ty2))

  let substitute phi (Forall (xs, ty)) = Forall (xs, Type.substitute phi ty)

  let instance (Forall (xs, t)) = forall xs t |> unbox

  let string_of_type_scheme (Forall (xs, ty)) =
    "∀"
    ^ Printer.separated " " (List.map Name.string_of_name xs)
    ^ "."
    ^ Type.string_of_type ty

end

(** {1 Explicitly-typed terms} *)

module XTerm : sig
  type t =
    | Var of Name.t * Type.t
    | App of t * t
    | Lam of Name.t * Type.t * t
    | Let of Name.t * TypeScheme.t * Name.t list * t * t
    | Lit of int
    | Exists of Name.t list * t

  val string_of_xterm : t -> string
end = struct
  type t =
    | Var of Name.t * Type.t
    | App of t * t
    | Lam of Name.t * Type.t * t
    | Let of Name.t * TypeScheme.t * Name.t list * t * t
    | Lit of int
    | Exists of Name.t list * t

  let string_of_type_variables xs =
    (String.concat " " (List.map Name.string_of_name xs))

  let rec string_of_xterm = function
    | Var (x, ty) ->
       Printf.sprintf "%s ≼ %s"
         (Name.string_of_name x)
         (Type.string_of_type ty)
    | App (t, u) ->
       Printf.sprintf "@(%s,%s)"
         (string_of_xterm t)
         (string_of_xterm u)
    | Lam (x, ty, t) ->
       Printf.sprintf "(λ(%s : %s). %s)"
         (Name.string_of_name x)
         (Type.string_of_type ty)
         (string_of_xterm t)
    | Let (x, s, xs, t, u) ->
       Printf.sprintf "(let %s : %s = ∀%s. %s in %s)"
         (Name.string_of_name x)
         (TypeScheme.string_of_type_scheme s)
         (string_of_type_variables xs)
         (string_of_xterm t)
         (string_of_xterm u)
    | Lit i ->
       string_of_int i
    | Exists (xs, t) ->
       Printf.sprintf "∃%s. %s"
         (string_of_type_variables xs)
         (string_of_xterm t)

end
