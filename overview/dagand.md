###  Type-Directed Programming

We revisit the notion of algebraic datatypes through their categorical
semantics as initial algebras (inductive types) and final coalgebras
(coinductive types). We show how recursive program definitions can be
distilled to a handful of recursion/corecursion schemes, thus enabling
general and systematic reasoning about such definitions. We
demonstrate how, in practice, these principles can be used to reason
about pure functional programs as well as derive efficient
implementations from high-level specifications.

We then study type classes, a mechanism that enables the concise
description of programs parameterized over an ad-hoc collection of
types. We provide a formal treatment of ad-hoc polymorphism in a
Haskell-like language. Aside from the foundational aspect, this first
step shall provide some operational intuitions for type classes. We
then explore the benefits of ad-hoc polymorphism from a programming
standpoint. We show how the usual hierarchy of algebraic structures
fits into this framework. We will cover functors (to abstract over
data containers), applicatives and monads (to abstract over effects),
foldable and traversable functors (to abstract over iterators) as well
as Neperian functors and lenses (to abstract over data accessors).

We conclude this journey by entering the realm of type-level
programming, first in a restricted, ML setting and then in a
full-spectrum, dependent type setting. Type-level programming enable
the precise transcription of the invariants of a program into its
type. It is a step toward "correct-by-construction" programming while
allowing the programmer to dispense with dynamic checks (run-time
assertions) in favor of static checks (delegated to the
type-checker). We provide a formal treatment of generalized algebraic
data types (GADTs) in an ML-like language. This restricted form of
type-level programming strikes a balance between expressiveness and
decidability. Besides, it is readily available in OCaml, allowing
further experimentation in class. We will develop several examples of
type-level programming, starting with tagless interpreters using GADTs
and gradually moving toward examples involving full-spectrum
dependent-types, as available in Agda or Coq.
