### Operational Semantics, Type Systems, and Program Transformations

In the first lecture, we discuss several presentations of the *operational
semantics* of a call-by-value functional programming language. We explain why
each of these presentations exists and in what sense these presentations are
equivalent. One of these presentations is in fact executable: it is an
interpreter.

In the following two lectures, we present the *polymorphic typed λ-calcuus*,
also known as *System F*. We use a syntactic technique to state and prove that
this type system is sound, that is, *well-typed programs cannot crash*. We
extend System F with several features, including algebraic data types,
existential types, and GADTs, and discuss why these features are useful
in real-world programming languages.

In the last two lectures, we present a few classic *program transformations*,
namely closure conversion, defunctionalization, and the continuation-passing
style (CPS) transformation. These program transformations are interesting from
two points of view. First, they are *useful programming techniques*, which can
help write or understand programs. Second, they are used in the *compilation*
of functional programming languages, so they help understand what happens when
the machine executes a program. We discuss how to *prove* that the meaning of
programs is preserved by these transformations, based on an operational
semantics.
