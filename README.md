# Functional programming and type systems (2017-2018)

## Teachers

   * Functional Programming: Under the Hood (12h30, [François Pottier](http://gallium.inria.fr/~fpottier))
   * Metatheory of Typed Programming Languages (12h30, [Didier Rémy](http://gallium.inria.fr/~remy/), *head*)
   * Advanced Aspects of Type Systems (12h30, [Yann Régis Gianas](http://www.pps.jussieu.fr/~yrg/))
   * Dependently-typed Functional Programming (12h30, [Pierre-Evariste Dagand](https://pages.lip6.fr/Pierre-Evariste.Dagand/))

## Aims

This course presents the principles and formalisms that underlie many of
today's typed functional programming languages.

The course is made up of four parts and can be split after the first two
parts.

In the first part, we discuss the *operational semantics* of functional
programming languages, and we present several classic *program
transformations*, including closure conversion, defunctionalization, and the
transformation into continuation-passing style (CPS). These program
transformations are interesting from two points of view. First, they are
*useful programming techniques*, which can help write or understand
programs. Second, they are used in the *compilation* of functional
programming languages, so they help understand what happens when the machine
executes a program. We use operational semantics to *prove* that the meaning
of programs is preserved by these transformations. Finally, we suggest how
these definitions and theorems can be expressed in a form that a machine can
check. That is, although Coq is not a prerequisite of the course, we will at
least try to *read and understand Coq definitions and statements*.

In the second part, we focus on the meta-theoretical properties of type
systems.  We study parametric polymorphism (as in System F and ML), data
types and type abstraction. We show syntactic type soundness (via progress
and subject reduction) by reasoning by induction on typing derivations.  We
also show how to obtain semantic properties via logical relations by
reasoning by induction on the structure of types.  We also introduce
subtyping and row polymorphism and illustrate typing problems induced by
side effects (references) and the need for the value restriction.

The third part of the course describes more advanced features of type
systems: exceptions and effect handlers, including their typechecking and
static analyses: type inference, data flow and control flow analyses.
Finally, it introduces dependent types and refinement types.

The last part focuses on the use of dependent types for programming:
effectful programming with monads and algebraic effects; tagless
interpreters; programming with total functions; generic programming.
We also show the limits of dependently-typed functional programming.

## Approximate syllabus

### Functional Programming: Under the Hood

* (22/09/2017) From a small-step operational semantics...
* (29/09/2017) ... to an efficient interpreter. (2 weeks.)
* (06/10/2017) Compiling away first-class functions: closure conversion, defunctionalization.
* (13/10/2017) Compiling away the call stack: the CPS transformation.
* (20/10/2017) Equational reasoning and program optimizations.

### Metatheory of Typed Programming Languages

* (15/09/2017) Metatheory of System F. (Type soundness. Erasure.)
* (27/10/2017) ADTs, existential types, GADTs. (Typed program transformations.)
* (03/11/2017) Logical relations.
* (17/11/2017) Sub(typing. Rows. (Covariant arrays and covariant functions!)
* (24/11/2017) References. (Value restriction.)

### Advanced Aspects of Type Systems

* Exceptions and effect handlers. (Compiled away via CPS.)
* Typechecking exceptions and handlers.
* Type inference. (ML. Bidirectional. Elaboration.)
* Data/control flow analysis.
* Functional correctness. Intro to dependent/refinement types.

### Dependently-typed Functional Programming

* Effectful functional programming.
* Dependent functional programming.
* Total functional programming.
* Generic functional programming.
* Open problems in dependent functional programming.

## Recommended software

OCaml 4.0x and Coq **8.5**.

Once you have installed [opam](https://opam.ocaml.org/doc/Install.html), use the following commands:
```bash
opam init --comp=4.05 # for instance
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install -j4 -v coq.8.5.3
```

## Bibliography

[Types and Programming Languages](https://mitpress.mit.edu/books/types-and-programming-languages),
Benjamin C. Pierce, MIT Press, 2002.
