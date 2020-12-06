(**This is the API of the "subcontinuation" monad, also known as the delimited
   continuation monad, as described in the paper "A Monadic Framework for
   Delimited Continuations", by Dybvig, Peyton Jones, and Sabry (2007). *)

(**A value of type ['a m] is a computation, which, when executed, can return a
   result of type ['a]. Such a computation can also perform control effects,
   that is, transform the evaluation context under which it is evaluated. *)
type 'a m

(**An evaluation context represents a context under which a computation is
   evaluated.

   The type [('a, 'b) context] can be read like a function type, where ['a]
   is the domain and ['b] is the codomain. Indeed, under a context of type
   [('a, 'b) context], one can evaluate a computation of type ['a m], and
   this operation forms a computation of type ['b m]. This is permitted by
   [push_subcont].

   A context of type [('a, 'b) context] can also be thought of as a partial
   stack. Then, ['a] is the type of the top of the stack (that is, the end
   of the stack where elements are pushed and popped), while ['b] is the
   type of the bottom of the stack.

   A context of type [('a, 'b) context] can also be thought of as a
   delimited continuation, that is, an effectful function, that is, a
   function of type ['a -> 'b m]. This view is directly supported by
   [apply_subcont]. *)
type ('a, 'b) context

(**The computation [return v] performs no effect and returns the value [v]. *)
val return: 'a -> 'a m

(**The computation [bind m1 m2] first executes [m1], yielding a result [v1],
   then executes [m2 v]. Thus, [bind] is a sequencing construct, where the
   second component of the sequence has access to the value produced by the
   first component of the sequence. *)
val bind: 'a m -> ('a -> 'b m) -> 'b m

(**[let* x = m1 in m2] is sugar for [bind m1 (fun x -> m2)]. *)
val (let*): 'a m -> ('a -> 'b m) -> 'b m

(**The exception [PromptNotFound] can be raised by [run]. *)
exception PromptNotFound

(**[run m] runs the computation [m] and returns its result. It is possible for
   this operation to fail. This happens if the computation [m] attempts to
   capture a continuation delimited by a prompt [p] at a time when this prompt
   does not appear on the stack. In such a case, [PromptNotFound] is raised. *)
val run: 'a m -> 'a

(**A prompt, also known as a delimiter, is a mark that can be pushed on the
   stack. A prompt has no direct effect on evaluation: the computation
   [push_prompt p (return v)] is equivalent to [return v]. The type of a
   prompt determines the type of the values that are returned through it: in
   [push_prompt p (return v)], if [p] has type ['a prompt], then [v] must have
   type ['a]. *)
type 'a prompt

(**The computation [new_prompt] creates and returns a fresh prompt. The type
   ['a] of the new prompt is chosen by the user. Although the computation
   [new_prompt] is polymorphic in ['a], each newly-created prompt is
   monomorphic and has type ['a prompt] for some fixed ['a]. *)
val new_prompt: 'a prompt m

(**The computation [push_prompt p m] first pushes the prompt [p] onto the
   stack; then, it executes the computation [m], yielding a result [v];
   finally, it pops [p] off the stack and returns [v]. *)
val push_prompt: 'a prompt -> 'a m -> 'a m

(**The computation [with_subcont p m] first searches the context for the
   nearest occurrence of the prompt [p]. (If the prompt [p] does not appear
   in the context, a runtime error occurs.) It splits the context at this
   prompt in two parts. (The prompt [p] itself appears in neither part.) The
   most recent part [c] of the context is captured. The most ancient part of
   the context remains in place, and the computation [m c] is executed under
   it. The operation [with_subcont] is also known as [cupto], as it captures
   the context up to the prompt [p]. *)
val with_subcont: 'b prompt -> (('a, 'b) context -> 'b m) -> 'a m

(**The computation [push_subcont c] first pushes the context [c] in front of
   the current evaluation context, then executes the computation [m]. *)
val push_subcont: ('a, 'b) context -> 'a m -> 'b m

(**[apply_subcont] converts a context to a delimited continuation, that is,
   an effectful function. [apply_subcont context x] is in fact defined as
   [push_subcont context (return x)]. *)
val apply_subcont: ('a, 'b) context -> 'a -> 'b m
