open Eq

(* This implementation of tags is due to Frédéric Bour. *)

(* The type ['a tags] is an extensible GADT. In a sense, it is the
   type of all tags that we seek. Yet, we cannot use it directly,
   because we have no way of defining an equality function of type
   ['a1 tags -> 'a2 tags -> ('a1, 'a2) eq option]. *)

type 'a tags = ..

(* So, instead, we define another type, ['a tag], as follows. *)

(* A value of type ['a tag] is a first-class module that contains
   a data constructor [T] and a proof that [T] has type ['a tags].
   The data constructor [T] can be used both as a value and as a
   pattern in a pattern-matching construct. *)

module type TAG = sig
  type t
  type 'a tags += T : t tags
end

type 'a tag = (module TAG with type t = 'a)

(* The function [new_tag] extends the type ['a tags] with a fresh data
   constructor [T] and packages it up as a first-class module. *)

let new_tag (type a) () : a tag =
  let module Tag = struct
    type t = a
    type 'a tags += T : t tags
  end in
  (module Tag)

(* The function [equal] expects two first-class modules as arguments and
   compares the data constructors [A.T] and [B.T]. Crucially, it does not use
   an equality test [A.T = B.T], which would have the desired semantics, but
   would be ill-typed. Instead, the data constructor [A.T] is used as a value,
   while the data constructor [B.T] is used as a pattern. Not only is this
   well-typed, but also, thanks to the magic of GADTs, in the first branch of
   the pattern-matching construct, the type equation [a = b] is available,
   allowing the type-checker to prove that [Eq] has type [(a, b) eq], as
   desired. *)

let equal (type a b) ((module A) : a tag) ((module B) : b tag)
: (a, b) eq option =
  match A.T with
  | B.T -> Some Eq
  | _   -> None
