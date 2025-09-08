### Monads as a Programming Tool and as a Semantic Tool

We put type classes, the mechanism for ad-hoc polymorphism seen in the previous lesson, to practice!

In the first lecture, we leverage them from a purely programming standpoint.
We show the benefits of well-known algebraic structures to describe effectful
computations using pure functions.
We consider notably functors (to abstract over data
containers), applicatives and selective functors, and monads (to abstract over effects),
and their use for programming.

We then see how monads may serve as a semantic tool as well.
We first consider the free monad as a generic, extensible syntax. After a detour
through a modicum of coinduction theory, we discuss Capretta's delay monad as a
means for internalizing divergence in type theory.
Putting things together, we arrive at interaction trees as a generic monad for modelling
diverging and effectful computations in type theory, and in particular the Rocq proof assistant.

We conclude our journey by discussing the question of giving semantics to the effectful operations represented
in such structures. After discussing the algebraic approach, we focus on monadic interpretation to
build executable interpreters built in layers.

