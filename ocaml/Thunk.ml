(* A thunk is in one of two states: either it has been evaluated already,
   so the result of the computation is known already; or it has not been
   evaluated yet, and we have a function, a suspended computation. *)

type 'a state =
| Evaluated of      (* result: *)          'a
| Suspended of (* computation: *) (unit -> 'a)

type 'a thunk =
  'a state ref

let create (f : unit -> 'a) : 'a thunk =
  ref (Suspended f)

let force (thunk : 'a thunk) : 'a =
  match !thunk with
  | Evaluated x ->
      x
  | Suspended f ->
      let x = f() in
      thunk := Evaluated x;
      x

(* This simple-minded implementation does not defend itself against cyclic
   thunks -- for instance, a thunk [t] whose suspended computation invokes
   [force t] again. In general, thunks form a graph in memory, and this
   graph be cyclic. In order to ensure that every thunk is evaluated at
   most once, one should use three colors instead of two, in the same way
   as a standard depth-first graph traversal uses three colors to detect
   cycles. When a cycle is detected, [force] should raise an exception.
   This is left as an exercise. *)

(* OCaml's built-in thunks have this cycle detection mechanism.

   let rec x : int Lazy.t = lazy (Lazy.force x + 1);;

   Lazy.force x;;

 *)
