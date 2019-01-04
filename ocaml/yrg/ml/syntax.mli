(** {1 Names} *)
module Name :
  sig
    type t

    (** [fresh printer] creates a fresh name displayed by [printer]. *)
    val fresh : (int -> string) -> t

    (** [refresh x] creates a fresh name inheriting printer from [x]. *)
    val refresh : t -> t

    (** [compare x y] is a total order over names. *)
    val compare : t -> t -> int

    (** [string_of_name x] pretty prints [x]. *)
    val string_of_name : t -> string
  end

module NameSet : Set.S with type elt = Name.t

module Substitution :
  sig
    type 'a t

    (** The [identity] substitution. *)
    val identity : 'a t

    (** [binding x v] rewrites [x] into [v]. *)
    val binding : Name.t -> 'a -> 'a t

    (** [compose trivial subst s1 s2] returns a substitution from names to
        values of type ['a] such that:
        - [trivial x v] returns [true] iff [x = v].
        - [subst s v] applies [s] to a value [v] of type ['a].
    *)
    val compose :
      (Name.t -> 'a -> bool) -> ('a t -> 'a -> 'a) -> 'a t -> 'a t -> 'a t

    (** [get s x] returns [Some v] is [x] maps to [v] in [s]. *)
    val get : 'a t -> Name.t -> 'a option

    (** [domain s] returns [xs] such that
        [x \in xs <-> exists v, get s x = Some v]. *)
    val domain : 'a t -> Name.t list

    (** [string_of_substitution printer s] returns a human-readable
        representation of [s] using [printer] to display values of
        type ['a]. *)
    val string_of_substitution : ('a -> string) -> 'a t -> string
  end

(** {1 Implicitly typed MiniML} *)
module ITerm :
  sig
    type t =
        Var of Name.t         (** x, y, z, ...   *)
      | App of t * t          (** t t            *)
      | Lam of Name.t * t     (** \lambda x. t   *)
      | Let of Name.t * t * t (** let x = t in t *)
      | Lit of int            (** 37, 73, 42, 13 *)
  end

module TypeConstructor :
  sig
    type t

    (** Every type constructor has an arity. *)
    val arity : t -> int

    (** Equality between type constructors is decidable. *)
    val equal : t -> t -> bool

    (** [arrow] constructs functional types. *)
    val arrow : t

    (** [int] is for integer literals. *)
    val int : t
  end

module Type :
  sig
    (** A type is a first-order term.

        This type definition is private: types can be inspected but not
        built using data constructors.

    *)
    type t = private Var of Name.t | App of TypeConstructor.t * t list

    (** [var x] constructs a type variable. *)
    val var : Name.t -> t

    (** [app t tys] constructs [App (t, tys)] raising [InvalidArity]
        is the arity of [t] is not respected. *)
    val app : TypeConstructor.t -> t list -> t
    exception InvalidArity of TypeConstructor.t * int * int

    (** [arrow a b] builds [a -> b]. *)
    val arrow : t -> t -> t

    (** a shortcut for [int]. *)
    val int : t

    (** [destruct_arrow (arrow a b)] returns [Some (a, b)],
        [None] on other value. *)
    val destruct_arrow : t -> (t * t) option

    (** Equality over types is decidable. *)
    val equal : t -> t -> bool

    (** [substitute s ty] applies [s] on [ty]. *)
    val substitute : t Substitution.t -> t -> t

    (** [free_type_variables ty] returns the free type variables of [ty]. *)
    val free_type_variables : t -> NameSet.t

    (** [string_of_type t] returns a human readable representation for [t]. *)
    val string_of_type : t -> string
  end

module TypeScheme :
  sig
    type t

    (** [forall xs t] is a type scheme parameterized by [xs]. *)
    val forall : Name.t list -> Type.t -> t

    (** [instance s] returns a fresh instance of [s]. *)
    val instance : t -> Name.t list * Type.t

    (** [substitute phi s] applies the substitution [phi] to the free
       type variables of [s]. *)
    val substitute : Type.t Substitution.t -> t -> t

    (** [free_type_variables s] returns the free type variables of [s]. *)
    val free_type_variables : t -> NameSet.t

    (** [string_of_type_scheme s] returns a human-readable
       representation for [s]. *)
    val string_of_type_scheme : t -> string
  end

module XTerm :
  sig

    (** An explicitly typed language, i.e. an encoding of typing derivations. *)
    type t =
      | Var of Name.t * Type.t
      (** [x ty] encodes the INST rule. *)
      | App of t * t
      (** [t t] *)
      | Lam of Name.t * Type.t * t
      (** [\lambda (x : ty). t] *)
      | Let of Name.t * TypeScheme.t * Name.t list * t * t
      (** [let x : s = t in t] *)
      | Lit of int
      (** [1, 31, 13, ...] *)
      | Exists of Name.t list * t
      (** [\exists xs. t] introduces fresh variables that can be used to
          denote /unknown/ types. *)

    (** [string_of_xterm t] returns a human readable representation of [t]. *)
    val string_of_xterm : t -> string
  end
