(* Exercises proposed at the end of the course

   Effects, lecture 0
   November 10th, 2021
*)

module type Monad = sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module Exercices (M : Monad) = struct
  open M
  let ( let* ) = bind

  (* TODO: define the functions below *)

  val join : 'b t t -> 'b t

  val strength : 'a * ('b t) -> ('a * 'b) t
  val pair : ('a t) * ('b t) -> ('a * 'b) t

  val traverse : 'a t list - > 'a list t
  val mapM : ('a -> 'b t) -> 'a list -> 'b list t
end

