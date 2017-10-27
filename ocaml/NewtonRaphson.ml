(* A couple abbreviations. *)

type 'a thunk = 'a Lazy.t
let force = Lazy.force

(* The definition of (finite or infinite) lazy lists. *)

type 'a stream =
  'a head thunk

and 'a head =
  | Nil
  | Cons of 'a * 'a stream

(* Calling [tail xs] demands the head of the stream, that is, forces
   the computation of the first element of the stream (if there is one). *)

let tail xs =
  match force xs with
  | Nil -> assert false
  | Cons (_, xs) -> xs

(* Newton-Raphson approximation, following Hughes,
   "Why functional programming matters", 1990. *)

let next n x =
  (x +. n /. x) /. 2.

(* An infinite stream obtained by iterating [f]. *)

(* The following definition, copied almost literally from Hughes'
   paper, is correct but somewhat unsatisfactory; can you see why? Can
   you fix it? Think about it before reading the solution below. *)

let rec repeat (f : 'a -> 'a) (a : 'a) : 'a stream =
  lazy (Cons (a, repeat f (f a)))

(*
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *)

(* In the above definition of [repeat], the function call [f a] takes
   place when the *first* element of the list is demanded by the consumer.
   That's too early -- ideally, this function call should take place only
   when the *second* element is demanded, since the result of [f a] is the
   second element in the infinite stream [a], [f a], [f (f a)], ... *)

(* This code exhibits the problem: *)

let () =
  let x = ref 0 in
  let f () = incr x; () in
  let xs = repeat f () in
  let xs = tail xs in
  (* This assertion fails because [x] has been incremented once: *)
  assert (!x = 0);
  ignore xs

(* This can be fixed in several ways. One solution is to let [repeat] take an
   argument of type ['a thunk] instead of ['a]. This approach is in fact the
   standard encoding of call-by-need into call-by-value, applied to Hughes'
   code. *)

let rec repeat (f : 'a -> 'a) (a : 'a thunk) : 'a stream =
  lazy (
    Cons (
      force a,
      repeat f (lazy (f (force a)))
    )
  )

(* It can also be written as follows. *)

let rec repeat (f : 'a -> 'a) (a : 'a thunk) : 'a stream =
  lazy (
    let a = force a in
    Cons (
      a,
      repeat f (lazy (f a))
    )
  )


(* We define a wrapper so [repeat] has the desired type again: *)

let repeat (f : 'a -> 'a) (a : 'a) : 'a stream =
  repeat f (lazy a)

(* The problematic code now behaves as desired: *)

let () =
  let x = ref 0 in
  let f () = incr x; () in
  let xs = repeat f () in
  (* These assertions succeed: *)
  let xs = tail xs in
  assert (!x = 0);
  let xs = tail xs in
  assert (!x = 1);
  let xs = tail xs in
  assert (!x = 2);
  ignore xs

(* Back to Newton-Rapshon. *)

let rec within (eps : float) (xs : float stream) : float =
  match force xs with
  | Nil -> assert false
  | Cons (a, xs) ->
      match force xs with
      | Nil -> assert false
      | Cons (b, _) ->
          if abs_float (a /. b -. 1.) <= eps then b
          else within eps xs

let sqrt (n : float) : float =
  within 0.0001 (repeat (next n) n)

let sqrt2 =
  sqrt 2.
