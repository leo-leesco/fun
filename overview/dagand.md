###  Typed Programming

We study type classes, a mechanism that enables the concise
description of programs parameterized over an ad-hoc collection of
types. We provide a formal treatment of ad-hoc polymorphism in a
Haskell-like language. Aside from the foundational aspect, this first
step shall provide some operational intuitions for type classes. We
then explore the benefits of ad-hoc polymorphism from a programming
standpoint.

We then show how the usual hierarchy of algebraic structures fits into
this framework. We will cover functors (to abstract over data
containers), applicatives and monads (to abstract over effects),
foldable and traversable functors (to abstract over iterators) as well
as Naperian functors (to abstract over data accessors).

We consider the challenging problem of bridging the gap between the
specification of a type system and its concrete implementation. To
this end, we cover two angles of attack. In a first lecture, we
consider a constraint-based approach, as it originates in the ML
tradition. In a second lecture, we consider a bidirectional approach,
as it originates in the dependently-typed tradition.

We conclude this journey by looking into "programming in the
large". To this end, we study F-omega as a structuring language to
organize modules and their composition.