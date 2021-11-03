(* This code uses MetaOCaml: *)
(* https://okmij.org/ftp/ML/MetaOCaml.html#install *)

(* To interpret this file in the OCaml REPL,
   use [metaocaml] instead of [ocaml]. *)

(* The following incantation is required for the type [code] to be known: *)
open Codelib

(* The following is required for the functions [run] and [print_code] to be
   known. Use [Runnative] when compiling to native code and [Runcode] when
   compiling to bytecode or interpreting this file in the OCaml REPL. *)
open Runnative
  (* in the REPL: open Runcode;; *)

(* -------------------------------------------------------------------------- *)

(* Streams. *)

(* This presentation follows the paper "Stream Fusion, to Completeness" by
   Kiselyov et al. (2017). *)

(* The "shape" of a stream is the information that we wish to obtain when we
   query a stream. This type definition is parameterized both over the type
   ['a] of the elements and over the type ['stream] of the remainder of the
   stream. It can serve as a basis for several different definitions of the
   type of streams. *)

(* MetaOCaml requires us to put this definition in its own module, Shape.

type ('a, 'stream) shape =
  | Nil
  | Cons of 'a * 'stream

 *)

open Shape
  (* in the REPL: #load "Shape.cmo";; *)

(* The type of a [fold] function on a sequence,

     ∀ω. (α → ω → ω) → ω → ω

   is isomorphic to:

     ∀ω. (α * ω → ω) → ω → ω           -- because A → B → C is A * B → C (currying)
     ∀ω. (α * ω → ω) → (1 → ω) → ω     -- because A is also 1 → A
     ∀ω. (α * ω → ω) * (1 → ω) → ω     -- by currying again
     ∀ω. ((1 + α * ω) → ω) → ω         -- because (A → C) * (B → C) is (A + B) → C
     ∀ω. ((α, ω) shape → ω) → ω        -- by definition of [shape]

  So, a "push stream", where the producer tells the consumer to process one
  more element (or the end of the sequence), can be defined as follows: *)

type 'a push_stream =
  { fold: 'omega. (('a, 'omega) shape -> 'omega) -> 'omega }

(* In a "pull stream", on the contrary, the consumer tells the producer to
   please produce the next element (or the end of the sequence). This is known
   as an [unfold]. This type definition can be understood as the description
   of an object that has opaque internal state [s] and a single method [step]
   that produces a shape.

   This is an existential type:

     α stream = ∃σ. σ * (σ → (α, σ) shape)

 *)

type 'a pull_stream =
  Stream : 'state * ('state -> ('a, 'state) shape) -> 'a pull_stream

(* From here on, we focus on pull streams. *)

(* Demanding the first element of a stream (if there is one). *)

let force (xs : 'a pull_stream) : ('a, 'a pull_stream) shape =
  (* Access [s] and [step]. *)
  let Stream (s, step) = xs in
  (* Request a shape. *)
  match step s with
  | Nil ->
      Nil
  | Cons (x, s) ->
      (* Re-package the new internal state [s] as a stream. *)
      Cons (x, Stream (s, step))

(* The [map] function on streams. *)

let map (f : 'a -> 'b) (xs : 'a pull_stream) : 'b pull_stream =
  (* Access [s] and [step]. *)
  let Stream (s, step) = xs in
  (* Define a new [step] function. *)
  let step s =
    match step s with
    | Nil ->
        Nil
    | Cons (x, s) ->
        Cons (f x, s)
  in
  (* Package [s] with the new [step] function. *)
  Stream (s, step)

(* The stream of the integers up to [n], excluded. *)

let ints (n : int) : int pull_stream =
  (* Define an initial state. *)
  let s = 0 in
  (* Define a [step] function. *)
  let step i =
    if i < n then
      let x = i
      and s = i + 1 in
      Cons (x, s)
    else
      Nil
  in
  (* Package [s] and [step]. *)
  Stream (s, step)

(* Creating a stream out of an array. *)

let of_arr (a : 'a array) : 'a pull_stream =
  (* Define an initial state. *)
  let s = (a, 0) in
  (* Define a [step] function. *)
  let step (a, i) =
    if i < Array.length a then
      let x = a.(i)
      and s = (a, i + 1) in
      Cons (x, s)
    else
      Nil
  in
  (* Package [s] and [step]. *)
  Stream (s, step)

(* Computing the sum of the elements of a stream of integers. *)

let rec sum (xs : int pull_stream) (accu : int) : int =
  (* This is a consumer: [force] is used. *)
  match force xs with
  | Nil ->
      accu
  | Cons (x, xs) ->
      sum xs (x + accu)

let sum xs =
  sum xs 0

(* A test. *)

let square x =
  x * x

let () =
  let n = 10 in
  let s = ints (n+1) |> map square |> sum in
  Printf.printf "The sum of the squares up to n=%d is %d.\n%!" n s
    (* expected: 385 *)

(* These naive streams work, but are slow, because they involve calls to
   unknown closures (such as the closure [step] that is created inside [map])
   and repeated construction and deconstruction of shapes. *)

(* From here on, we begin using double semicolons ;; because Tuareg mode is
   otherwise confused by MetaOCaml's syntax and can't find the boundaries
   between toplevel phrases. *)

(* -------------------------------------------------------------------------- *)

(* Staged streams. Kiselyov et al., Section 4.2. *)

(* We want to optimize [map] for the common case where the function [f] is
   known at stage 1, but the stream [xs] is not known until stage 2.

   This means that instead of an opaque function of type α → β, we want [f] to
   be a piece of code of type β, with a single hole of type α. This can be
   represented as a function of type ⟨α⟩ → ⟨β⟩.

   Thus, the type of [map] should be (⟨α⟩ → ⟨β⟩) → α stream -> β stream. *)

(* Also, in a stream, which is a pair of a state [s] and a [step] function,
   we do not expect the state to be known until stage 2, but we can require
   the [step] function to be known at stage 1, because we know how streams
   are constructed.

   So, the type of the state changes from σ to ⟨σ⟩,

   and the type of the [step] function becomes ⟨σ⟩ → ⟨(α, σ) shape⟩. *)

type 'a stream1 =
  Stream1 :
    'state code *
    ('state code -> ('a, 'state) shape code)
    -> 'a stream1

(* Quoting Kiselyov, it is now "straightforward" to write [map]. *)

let map (f : 'a code -> 'b code) (xs : 'a stream1) : 'b stream1 =
  (* Access [s] and [step]. *)
  let Stream1 (s, step) = xs in
  (* Define a new [step] code. This time, the function application [step s],
     which we can execute in stage 1, produces a piece of code whose type is
     [('a, 'state) shape]. We want to wrap this code in a [match] contruct
     that takes place at stage 2. Hence, we place quotes .< >. around the
     [match] construct and antiquote .~( ) around the call [step s].

     Furthermore, the function [f] is now a stage-1 function, not a stage-2
     function. We must apply [f] at stage 1 to the code fragment that consists
     of just the stage-2 variable [x]. Hence, we place an antiquote around the
     call to [f], and we apply [f] to the quoted variable .<x>. *)
  let step s =
    .< match .~(step s) with
    | Nil ->
        Nil
    | Cons (x, s) ->
        Cons (.~(f .<x>.), s)
    >.
  in
  (* Package [s] with the new [step] function. *)
  Stream1 (s, step)
;;

(* The stream of the integers up to [n], excluded. *)

let ints (n : int) : int stream1 =
  (* Define an initial state. *)
  let s = .< 0 >. in
  (* Define the [step] code. *)
  let step s = .<
    let i = .~(s) in
    if i < n then
      let x = i
      and s = i + 1 in
      Cons (x, s)
    else
      Nil
  >. in
  (* Package [s] and [step]. *)
  Stream1 (s, step)
;;

(* Creating a stream out of an array. *)

(* A subtlety is that MetaOCaml apparently refuses to apply cross-stage
   persistence (CSP) to an array: attempting to do so results in the
   construction of ill-formed code at runtime.

   In other words, an array that has been allocated at stage 1 in the heap
   must not be mentioned in a piece of code that is intended to be executed
   at stage 2.

   To work around this limitation, we change [of_arr] to expect an argument
   of type ['a array code] instead of ['a array]. That is, [of_arr] does not
   expect at an actual array (one that already exists), but a piece of code
   that constructs an array. *)

let of_arr (a : 'a array code) : 'a stream1 =
  (* Define an initial state. *)
  let s = .< (.~(a), 0) >. in
  (* Define the [step] code. *)
  let step s =
    .< let (a, i) = .~(s) in
    if i < Array.length a then
      let x = a.(i)
      and s = (a, i + 1) in
      Cons (x, s)
    else
      Nil >.
  in
  (* Package [s] and [step]. *)
  Stream1 (s, step)
;;

(* Computing the sum of the elements of a stream of integers. *)

(* I am not sure if [sum] can be defined in terms of an auxiliary [force],
   as was the case above; here, I give a direct definition. *)

let sum (xs : int stream1) : int code =
  (* Access [s] and [step]. *)
  let Stream1 (s, step) = xs in
  (* Generate code for a loop. In the loop body, the stage-2 variable [s]
     represents the current state of the iteration. We apply [step] to the
     variable [s] in stage 1, yielding a code fragment that produces the
     current shape. We then wrap this code in a stage-2 case analysis. *)
  .< let rec loop s accu =
       match .~(step .<s>.) with
       | Nil ->
           accu
       | Cons (x, s) ->
           loop s (x + accu)
     (* At the beginning, the initial state [s] is used. *)
     in loop .~(s) 0 >.
;;

(* To obtain an integer sum, we must run the code produced by [sum xs].
   We do so, below, simply by composing [sum] and [run]. *)

(* A test. *)

(* This [square] has type [int code -> int code]: it is a code fragment
   of type [int] with a hole of type [int]. This is a suitable argument
   for [map]. *)

let square x =
  .< .~(x) * .~(x) >.
;;

let example n : int code =
  ints (n+1) |> map square |> sum
;;

let () =
  let n = 10 in
  let s = run (example n) in
  Printf.printf "The sum of the squares up to n=%d is %d.\n%!" n s
    (* expected: 385 *)
;;

(* The generated code can be printed as follows: *)

let () =
  let n = 10 in
  let code = example n in
  print_code Format.std_formatter code
;;

(* For the above example, the code produced by [sum] looks like this:

   let rec loop s accu =
     match
       match
         let i = s in
         if i < 11 then
           let x = i and s = i + 1 in
           Cons (x, s)
         else Nil
       with
       | Nil ->
           Nil
       | Cons (x, s) ->
           Cons (x * x, s)
     with
     | Nil ->
         accu
     | Cons (x, s) ->
         loop s (x + accu)
   in
   loop 0 0

   This code does not construct or invoke any closures. This is an improvement
   over the naive (unstaged) code.

   One can see that, for every integer comprised between 0 and 10 (included),
   two [Cons] cells are allocated: one cell is constructed by [ints] when this
   integer is produced, and one cell is constructed by [map] when this integer
   is squared.

   Thus, a lot of construction and deconstruction of shapes is still going on.
   This is inefficient: memory allocation and case analyses are required at
   runtime.

   To do better, we must stage the code in a different way.
   This requires insight. *)

(* -------------------------------------------------------------------------- *)

(* Staged streams. Kiselyov et al., Section 5.1. *)

(* Every stream consumer must be prepared to handle both shapes, [Nil] and
   [Cons], and this requires a case analysis to appear at stage 2. Indeed,
   the result type of the [step] function is [('a, 'state) shape code], so
   the shape is constructed at stage 2 and must be deconstructed (analyzed)
   also at stage 2. *)

(* Now, since every stream consumer must be prepared to handle [Nil] and must
   be prepared to handle [Cons], instead of letting the consumer construct
   *one* piece of code that handles all possible shapes, we can ask the
   consumer to provide *two* pieces of code, one that handles [Nil] and
   one that handles [Cons]. Or, equivalently, we can ask the consumer to
   provide a *stage-1 function* of a shape to a code fragment. *)

(* One piece of intuition is as follows. Instead of returning a shape
   A + B, one can switch to continuation-passing style and return the
   type ∀ω. ((A + B) → ω) → ω. This more complex type allows us to
   play with the placement of the code type constructor ⟨...⟩ in such
   a way that the shape is constructed and deconstructed in stage 1. *)

(* The type of the state is unchanged; it is still ⟨σ⟩. *)

(* The type of the [step] function was ⟨σ⟩ → ⟨(α, σ) shape⟩.

   We keep the domain ⟨σ⟩ → ...

   We change the codomain by switching to continuation-passing style
   and by playing with the placement of the code type constructor ⟨...⟩.
   The codomain becomes

     ∀ω. ((⟨α⟩, ⟨σ⟩) shape → ⟨ω⟩) → ⟨ω⟩

 *)

type 'a stream2 =
  Stream2 : {
    s   : 'state code;
    step: 'omega.
          'state code ->
          (('a code, 'state code) shape -> 'omega code) -> 'omega code
  } -> 'a stream2

(* Although this is quite complex, one thing is clear: we no longer see
   [_ shape code], so we no longer construct and deconstruct shapes in
   stage 2; instead, we see [(_ code, _code) shape], which means that
   shapes must be constructed and deconstructed at stage 1. *)

(* The [map] combinator becomes: *)

let map (f : 'a code -> 'b code) (xs : 'a stream2) : 'b stream2 =
  (* Access [s] and [step]. *)
  let Stream2 { s; step } = xs in
  (* Define a new [step] function, in CPS style. *)
  let step s k =
    (* We still want to invoke [step s], but this time, we must provide
       a continuation, which indicates how we wish to handle [Nil] and
       [Cons]. This continuation is a stage-1 function. It receives a
       shape as an argument. *)
    step s (fun shape ->
      match shape with
      | Nil ->
          (* We return [Nil], in CPS style, by invoking [k]. *)
          k Nil
      | Cons (x, s) ->
          (* Both [x] and [s] are code fragments, of type ['a code] and
             ['state code]. The stage-1 function application [f x] yields
             a new code fragment, of type ['b code], which represents the
             element that we wish to produce. We bind this expression to
             a variable [y] in the generated code, then we pass to the
             continuation [k] a [Cons] cell that holds the code fragments
             .<y>. and [s]. *)
          .< let y = .~(f x) in
             .~(k (Cons (.<y>., s))) >.
          (* Subtle point A. The reason why we introduce the variable [y]
             is that if we passed the code fragment [f x] directly to the
             continuation [k], then we would run the risk that this code
             fragment might be duplicated by the continuation. (I think.)
             Passing the code fragment .<y>. removes the risk; it is OK
             to duplicate a variable. *)
          (* Subtle point B. Returning a code fragment at this point is
             permitted because the definition of the type [stream2] uses
             the answer type ['omega code]. If we had instead used ['omega],
             an opaque answer type, this would have been disallowed. *)
    )
  in
  (* Package [s] with the new [step] function. *)
  Stream2 { s; step }
;;

(* The stream of the integers up to [n], excluded. *)

let ints (n : int) : int stream2 =
  (* Define an initial state. *)
  let s = .< 0 >. in
  (* Define [step]. *)
  let step s k = .<
    let i = .~(s) in
    if i < n then
      let x = i
      and s = i + 1 in
      .~(k (Cons (.<x>., .<s>.)))
    else
      .~(k Nil)
  >. in
  (* Package [s] and [step]. *)
  Stream2 { s; step }
;;

(* Computing the sum of the elements of a stream of integers. *)

let sum (xs : int stream2) : int code =
  (* Access [s] and [step]. *)
  let Stream2 { s; step } = xs in
  (* Generate code for a loop. As before, we apply [step] to [s] in stage 1,
     and unlike before, we also provide a stage-1 continuation. *)
  .< let rec loop s accu =
       .~(step .<s>. (fun shape ->
           match shape with
           | Nil ->
               .<accu>.
           | Cons (x, s) ->
               .<loop .~(s) (.~(x) + accu)>.
        ))
     (* At the beginning, the initial state [s] is used. *)
     in loop .~(s) 0 >.
;;

(* A test. *)

(* Same [square] function as above. *)

let example n : int code =
  ints (n+1) |> map square |> sum
;;

let () =
  let n = 10 in
  let s = run (example n) in
  Printf.printf "The sum of the squares up to n=%d is %d.\n%!" n s
    (* expected: 385 *)

(* The generated code can be printed as follows: *)

let () =
  let n = 10 in
  let code = example n in
  print_code Format.std_formatter code
;;

(* The generated code looks like this:

   let rec loop s accu =
     let i = s in
     if i < 11 then
       let x = i and s = i + 1 in
       let y = x * x in
       loop s (y + accu)
     else accu
   in
   loop 0 0

   This is essentially the best code that one can write in OCaml:
   a loop that uses two registers [s] and [accu]. *)

(* Our first attempt at staging streams contained nested [match] constructs.
   What we have done here, in a way, is that we used staging annotations to
   program a "case-of-case" transformation. The approach that we have followed
   may seem somewhat heavy, but is actually quite robust; it does not rely on
   compiler heuristics; instead, the MetaOCaml has a well-defined semantics
   and produces a predictable result. Just by looking at the definition of
   the type [_ stream2], one can tell that the type [shape] is not involved
   in stage 2, so we can be assured that no construction or deconstruction
   of shapes appears in the generated code. *)

(* -------------------------------------------------------------------------- *)

(* One can go further, and do better, e.g. by generating [for] loops when this
   is possible. In the example above, that would not make much difference, but
   in general, streams based on [for] loops are interesting, as they support
   efficient implementations of some operations, such as [length], [take], and
   [drop]. See Kiselyov et al., Section 5.3 and on, for a library where streams
   are represented (when possible) as "push streams" that generate [for] loops
   and (otherwise) as "pull streams" that generate [while] loops. *)
