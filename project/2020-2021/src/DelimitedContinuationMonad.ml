(* This file implements the "subcontinuation" monad, also known as the delimited
   continuation monad, which is described in the paper "A Monadic Framework for
   Delimited Continuations", by Dybvig, Peyton Jones, and Sabry (2007). Our
   implementation is inspired by Dybvig et al.'s first implementation, which is
   given in Sections 7.1, 7.2 and 7.3 of the paper, but improves on it in two
   ways, indicated in the comments below. *)

open Tag

(* Once you are done writing the code, remove this directive,
   whose purpose is to disable several warnings. *)
[@@@warning "-27-32-37-39"]

(* -------------------------------------------------------------------------- *)

(* A prompt is a tag. *)

type 'a prompt =
  'a tag

(* If desired, we could reveal the existence of an equality test on prompts,
   implemented by [Tag.equal]. This might be useful in some applications. *)

(* -------------------------------------------------------------------------- *)

(* The following four type definitions are mutually recursive. *)

(* We use a CPS monad: a computation is a function of a context to an answer.
   We improve upon Dybvig, Peyton Jones, and Sabry's Haskell implementation by
   enforcing the invariant that every computation is polymorphic in the type
   ['answer]. *)

(* OCaml is not System F: universal quantification is not part of the syntax
   of types. A polymorphic function type must be encapsulated inside a record
   type. See Section 5.3 of the manual, "Higher-rank polymorphic functions".
   https://caml.inria.fr/pub/docs/manual-ocaml/polymorphism.html#s:higher-rank-poly
 *)

type 'a m (* TASK: define this type. *)

(* A context (also known as a delimited continuation) is not represented as a
   function; it is represented as a data structure, that is, a stack.

   When thinking of a context as a function, we prefer to write its type under
   the form [('top, 'bot) context], which can be read like the function type
   ['top -> 'bot].

   When thinking of a context as a stack, we prefer to write its type under
   the form [('bot, 'top) stack], because we write our stacks from left to
   right. The left end is the bottom; the right end is the top. Elements are
   pushed and popped at the top. *)

and ('top, 'bot) context =
  ('bot, 'top) stack

(* As in Dybvig et al.'s paper, a stack is a sequence of elements of two
   kinds: 1- ordinary frames; 2- prompts. See page 11 of the paper, where
   the syntax of stacks is E ::= [] | D : E | p : E. In our terminology,
   E is a context, D is a frame, p is a prompt. *)

(* As in Dybvig et al.'s paper, the type [('bot, 'top) stack] is
   parameterized by the type ['top] of the values that flow into
   the stack and by the type ['bot] of the values that flow out of
   the stack. For this reason, the type [stack] is a GADT. *)

(* We improve upon Dybvig et al.'s paper by imposing the invariant that a
   stack cannot contain two consecutive frames. That is, two frames must be
   separated by at least one prompt. This invariant is not visible in the
   following type definition, but is enforced in our code. Thanks to this
   invariant, it is possible to jump from one prompt to the next prompt
   in time O(1). *)

and ('bot, 'top) stack (* TASK: define this type. *)

(* A frame of type [('bot, 'top) frame] is an ordinary evaluation
   context, that is, an evaluation context that does not contain
   any prompt. It can be represented as an effectful function of
   type ['top] to ['bot]. *)

and ('bot, 'top) frame (* TASK: define this type. *)

(* -------------------------------------------------------------------------- *)

(* The smart constructor [cons] enforces the invariant that a stack cannot
   contain two consecutive [SFrame] constructors. It exploits the auxiliary
   function [compose], which composes two frames into a single frame. As the
   definition of [compose] involves [bind], and as [bind] itself depends on
   [cons], the following three definitions must be mutually recursive. *)

let rec bind
: type a b .
  a m -> (a -> b m) -> b m
= assert false (* TASK: define this function. *)

and cons
: type bot mid top .
  (bot, mid) stack -> (mid, top) frame -> (bot, top) stack
= assert false (* TASK: define this function. *)

and compose
: type bot mid top .
  (bot, mid) frame -> (mid, top) frame -> (bot, top) frame
= assert false (* TASK: define this function. *)

(* Sugar. *)

let (let*) =
  bind

(* -------------------------------------------------------------------------- *)

(* [apply] applies a context to a value, producing an answer. *)

(* [apply] can be viewed as the function that interprets a defunctionalized
   continuation of type [('a, 'b) context] as a function of type ['a -> 'b]. *)

(* [apply] can also be understood as the operation of filling an evaluation
   context with a value, and continuing execution from there. *)

let rec apply
: type a b . (a, b) context -> a -> b
= assert false (* TASK: define this function. *)

(* This is the standard definition of [return] in a CPS monad. *)

let return
: type a . a -> a m
= assert false (* TASK: define this function. *)

(* This is the standard definition of [run] in a CPS monad. *)

let run
: type a . a m -> a
= assert false (* TASK: define this function. *)

(* -------------------------------------------------------------------------- *)

(* The definitions of [new_prompt] and [push_prompt] are straightforward. *)

let new_prompt
: type a. a prompt m
= assert false (* TASK: define this function. *)

let push_prompt
: type a. a prompt -> a m -> a m
= assert false (* TASK: define this function. *)

(* -------------------------------------------------------------------------- *)

(* [append stack1 stack2] is the concatenation of the stacks [stack1]
   and [stack2]. *)

(* The smart constructor [cons] is used (where appropriate) so as to
   respect the invariant that a stack cannot contain two consecutive
   [SFrame] constructors. *)

let rec append
: type bot mid top .
  (bot, mid) stack -> (mid, top) stack -> (bot, top) stack
= assert false (* TASK: define this function. *)

(* [push_subcont] performs a stack concatenation operation. *)

let push_subcont
: type a b . (a, b) context -> a m -> b m
= assert false (* TASK: define this function. *)

(* [apply_subcont] is a simple combination of [push_subcont] and [return]. *)

let apply_subcont
: type a b . (a, b) context -> a -> b m
= assert false (* TASK: define this function. *)

(* -------------------------------------------------------------------------- *)

(* [split tag stack] searches the stack [stack] for the tag [tag]. If it is
   found, then [stack] is split into three parts: a partial stack [back], the
   prompt [p], and a partial stack [front]. The pair [(back, front)] is
   returned. If the tag [p] is not found, then [PromptNotFound] is raised. *)

(* Because the stack cannot contain two consecutive [SFrame] constructors,
   we are able to jump from one prompt to the next prompt in time O(1).
   Thus, the time complexity of [split p] is linear in the number of
   prompts that have been pushed onto the stack after [p] was pushed. *)

exception PromptNotFound

let rec split
: type bot mid top .
  mid tag ->
  (bot, top) stack ->
  (bot, mid) stack * (mid, top) stack
= assert false (* TASK: define this function. *)

(* [push_subcont] performs a stack splitting operation. *)

let with_subcont
: type a b . b prompt -> ((b, a) stack -> b m) -> a m
= assert false (* TASK: define this function. *)
