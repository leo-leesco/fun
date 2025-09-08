### Syntax, Operational Semantics, and Type Systems

This part of the course is devoted to a *syntactic* view of programming
languages. In this view, programs and types are just pieces of syntax;
the behavior of programs is described by an *operational semantics*,
that is, a collection of rewriting rules; and the property of being
a well-typed program is defined by a *typing judgment*, that is,
a collection of deduction rules.

This syntactic view is simple and very
effective. It contrasts with a so-called *semantic* view where
one attempts to explain the *meaning* of programs or the meaning
of types via more elaborate mathematical constructions,
such as logical relations. This semantic view is the subject
of [the second part](overview/scherer.md) of the course.

In the first lecture, we discuss several presentations of the *operational
semantics* of a call-by-value functional programming language. We explain why
each of these presentations exists and in what sense these presentations are
equivalent. One of these presentations is in fact executable: it is an
interpreter.

In the following three lectures, we present several type systems
of increasing complexity, starting with the *simply-typed λ-calculus*
and continuing with the *polymorphic typed λ-calculus*,
also known as *System F*. We use a syntactic technique to state and prove that
these type systems are sound, that is, *well-typed programs cannot crash*. We
extend System F with several features, including algebraic data types,
existential types, and GADTs, and discuss why these features are useful
in real-world programming languages.

In the fifth lecture, we present two classic *program transformations*,
namely closure conversion and defunctionalization.
These program transformations are interesting from
two points of view. First, they are *useful programming techniques*, which can
help write or understand programs. Second, they are used in the *compilation*
of functional programming languages, so they help understand what happens when
the machine executes a program. We discuss how to *prove* that the meaning of
programs is preserved by these transformations, based on an operational
semantics.

The sixth and seventh lectures (by Gabriel Scherer) concern *type inference*
(via two quite different approaches, namely type inference based on equality
constraints and bidirectional type inference) and the extension of System F
with *mutable state*.
