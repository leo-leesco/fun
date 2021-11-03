# Functional programming and type systems (2021-2022)

This page supplements
[the official page of MPRI 2-4](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-4-2).

## Location and schedule

The lectures take place at University of Paris,
Bâtiment Sophie Germain, in room **1002**.

They are scheduled on **Wednesdays** from 12:45 to 15:30.
There is a 15-minute break in the middle of each lecture,
so each lecture lasts 2h30.

## Teachers

* Metatheory of typed programming languages
  ([Didier Rémy](http://cambium.inria.fr/~remy/), *head*)
* Interpretation, compilation, and program transformations
  ([François Pottier](http://cambium.inria.fr/~fpottier/))
* Effects
  ([Gabriel Scherer](http://www.lix.polytechnique.fr/Labo/Gabriel.Scherer/))
* Type-directed programming
  ([Pierre-Evariste Dagand](https://www.irif.fr/~dagand/))
* Rust: programming safely with resources in a modern low-level programming
  language ([Jacques-Henri Jourdan](https://jhjourdan.mketjh.fr/))

## Aims

This course presents the principles and formalisms that underlie many of
today's typed programming languages.
(Here are some [introductory slides](slides/fpottier-00.pdf).)

This year, the course is reorganized with new material and new teachers.
It is composed of five parts and cannot be split.

### Metatheory of Typed Programming Languages

<!-- We focus on the meta-theoretical properties of type systems.  We study
parametric polymorphism (as in System F and ML), data types and type
abstraction. We show syntactic type soundness (via progress and subject
reduction) by reasoning by induction on typing derivations.  We also show
how to obtain semantic properties via logical relations by reasoning by
induction on the structure of types.  Finally, we introduce subtyping, row
polymorphism, and illustrate the problems induced by side effects
(references) and the need for the value restriction.  -->

This part of the course is split in four lectures.  We first introduce the
_explicitly typed_ version of System F.  We prove its type soundness by
_subject reduction_ and _progress_.  We discuss _type erasing_ versus _type
passing_ semantics and derive the _implicitly typed_ version of System
F. We present _ML_ as a restriction of _System F_ to prenex polymorphism.
The definition and main properties of System F will also be mechanized in
the Coq proof assistant.

We then extend _System F_ with primitive datatypes, including variants and
records, and show their Church encodings.  We discuss both _iso-recursive_
and _equi-recursive_ types.  We present _existential types_.  _Generalized
Abstract Datatypes (GADTs)_ will just be introduced.

We also extend System-F with higher-order kinds and higher-order types,
which requires computation at the level of types, leading to system _F-omega_.
<!-- We may present _modules_ by elaboration into Fomega. -->

Finally, we introduce logical relations to show parametricity properties of
System F.  Unary relations are used to proof termination as an introduction
to logicial elations.  We cover binary relations in details. They allow to
prove _observational equivalence_ results or study the inhabitants at
certain polymorphic types.  We just introduce _step-indexed_ logical
relations which are needed when the programming language is extended with
constructs that enable unstructured forms of recursion, such as recursive
types at negative occurrences, or references.

### Interpretation, Compilation, and Program Transformations

In the first lecture, we discuss several presentations of the *operational
semantics* of a (call-by-value) functional programming language. We explain
why each of these presentations exists and in what sense these presentations
are equivalent. One of these presentations is in fact executable: it is an
interpreter. This interpreter can be implemented in Coq and can be *verified*,
that is, can be proved correct with respect to the other presentations of the
operational semantics. As far as time permits, we will review how lambda-terms
and their operational semantics can be defined in Coq, using a representation
of names as de Bruijn indices. Although Coq is not a prerequisite of the
course, we will at least try to *read and understand Coq definitions and
statements*.

In the next three lectures, we present several classic *program
transformations*, including closure conversion, defunctionalization, the
transformation into continuation-passing style (CPS), and stream fusion. These
program transformations are interesting from two points of view. First, they
are *useful programming techniques*, which can help write or understand
programs. Second, they are used in the *compilation* of functional programming
languages, so they help understand what happens when the machine executes a
program. We discuss how to *prove* that the meaning of programs is preserved
by these transformations, based on an operational semantics. We suggest how
these definitions and theorems can be expressed in a form that a machine can
check (that is, in Coq).


### Effects

In the theory of programming languages, "effects" describe
computational phenomenons that happen "on the side" during the
computation of a program. "While this function runs, it prints
messages / sends emails / displays images / accesses a database / asks
questions to the user, in addition to returning a result." Effects are
of course very important in programs, they are often the main
reason why humans execute programs in the first place!

There is an active research area studying effects: how to model them
mathematically, how to reason about programs containing effects, how
to implement them. Over time researchers realized that we can reuse
the theoretical analysis of effects to provide general mechanisms
letting programmers *implement* effects as libraries, instead of
having only a fixed set of effects supported by the programming
language definition. It is sometimes possible, through careful
refactoring, to take a complex program that computes various things
"directly", turn some of these things into "effects done on the side",
to obtain an equivalent program that looks simpler, is easier to write
and to understand -- with more complex effects on the side.

In this section of the course we will study:

- Algebraic structures that capture notions of effects in
  theory and in practice: monads and applicative functors.

- Effect handlers, a new programming construct that provides another,
  flexible approach to user-defined effects.

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


### Rust

In this part, we propose to give both a practical and a theoretical
view of the Rust programming language. This new language, developed
during the last decade, aims at modernizing systems programming by
providing a new balance between performance and control on the one
hand, and safety and ease of use on the other hand.

We will first give an overview of the language, from a user's
perspective. Rust got inspiration from many other programming
languages and adapted many well-known mechanisms to its contexts. We
will hence discuss features such as algebraic data types,
polymorphism, type traits (i.e., Rusts' type classes), closures and
subtyping. But Rust also introduced concepts which were only used in
experimental languages, such as ownership and aliasing
control. Finally, we will show how the type system of Rust allows
escaping from the safe fragment and encapsulating these uses of unsafe
features behind safe interfaces. We will study the important example
of interior mutability.

Next, we will focus on two recent research subjects on Rust. First, it
is possible to translate programs written in the safe fragment of Rust
into a functional language, thus completely erasing state. This makes
it possible to ease verification of Rust programs. Second, we will
give an overview of one proof of soundness of the type system of Rust,
which also proves that many libraries written in the unsafe fragment
are, in fact, safe.


## Programming Project

Since we are studying programming languages and their formalization,
programming is also an important part of the course. We give a mandatory
programming project (around the end of October) which must be completed
roughly by the end of January. The programming project counts for about a
third of the final grade.

<!-- The [programming project](project/2020-2021/) is now available;
read the [assignment](project/2020-2021/sujet.pdf).

The deadline for submitting your project is **January 27, 2021**.

Please do not hesitate to ask questions about the project,
of an administrative or technical nature,
to [François Pottier](francois.pottier@inria.fr).

Here are answers to some of the questions that have been asked:
-->

## Paper discussions (NEW!)

This course will include in-course discussion of research
articles/papers. We will read three papers during the semester. You
will be told about each one several weeks in advance; you have to read
it before the corresponding class, and we will discuss it together
during class. This should give you a glimpse of current topics in the
area, and more generally train you to read research papers and engage
with them.

## Research Internship Proposals

We have posted the following internship proposals (possibly more to come):

* [Verifying Tail-Call Optimization Modulo Constructor in Iris](https://cambium.inria.fr/~fpottier/stages/sujet2022-m2.pdf)

Please do not hesitate to talk to us (during the break or at the end of each
lecture), to contact us by email, or to visit us at our offices.

## Approximate Syllabus

### Interpretation, Compilation, and Program Transformations (introduction)

* (15/09/2021) Syntax, semantics, and interpreters.
  * Introduction to this course
      ([slides 00](slides/fpottier-00.pdf)).
  * Operational semantics and reduction strategies
      ([slides 01a](slides/fpottier-01a.pdf)).
  * Towards machine-checked definitions and proofs
      ([slides 01b](slides/fpottier-01b.pdf))
      ([λ-calculus in Coq](coq/DemoSyntaxReduction.v))
      ([λ-calculus in OCaml](ocaml/pottier/Lambda.ml)).
  * From a small-step semantics
    down to an efficient verified interpreter,
    in several stages
      ([slides 02](slides/fpottier-02.pdf))
      ([Coq repo](coq/)).

### Metatheory of Typed Programming Languages

* (22/09/2021)
  [Metatheory of System F](http://cambium.inria.fr/~remy/mpri/slides1.pdf)
  [(handout)](http://cambium.inria.fr/~remy/mpri/handout1.pdf);
  see chap [1,2,3](http://cambium.inria.fr/~remy/mpri/cours1.pdf)
  and [4](http://cambium.inria.fr/~remy/mpri/cours2.pdf)
  of [course notes](http://cambium.inria.fr/~remy/mpri/cours.pdf)).
  See also _a (slow) walk through the garden of type soundness proofs_
  in Coq, by François Pottier ([Coq repo](coq/), [html](coq/html/));
  to view the proofs online, please use the following links:
  - Lambda Calculus:
    [Syntax](http://cambium.inria.fr/~fpottier/mpri/html/LambdaCalculusSyntax.html),
    [Values](http://cambium.inria.fr/~fpottier/mpri/html/LambdaCalculusValues.html),
    [Reduction](http://cambium.inria.fr/~fpottier/mpri/html/LambdaCalculusReduction.html)
  - Simply-typed lambda-calculus:
    [definitions](http://cambium.inria.fr/~fpottier/mpri/html/STLCDefinition.html),
    [lemmas](http://cambium.inria.fr/~fpottier/mpri/html/STLCLemmas.html),
    [type
    soundness](http://cambium.inria.fr/~fpottier/mpri/html/STLCTypeSoundnessComplete.html).
  - The polymorphic lambda-calculus, also known as System F:
    [definitions](http://cambium.inria.fr/~fpottier/mpri/html/SystemFDefinition.html),
    [lemmas](http://cambium.inria.fr/~fpottier/mpri/html/SystemFLemmas.html),
    [type soundness
    ](http://cambium.inria.fr/~fpottier/mpri/html/SystemFTypeSoundnessComplete.html).
* (29/09/2021)
  [ADTs, existential types, GADTs](http://cambium.inria.fr/~remy/mpri/slides2a.pdf)
  ([handout](http://cambium.inria.fr/~remy/mpri/handout2.pdf)
   [without](http://cambium.inria.fr/~remy/mpri/handout2a.pdf) or
   [only](http://cambium.inria.fr/~remy/mpri/handout2b.pdf)
   the extra material);
  see also [chap 6](http://cambium.inria.fr/~remy/mpri/cours4.pdf)
   of [course notes](http://cambium.inria.fr/~remy/mpri/cours.pdf).
  _(Lesson 2 ended at slide 57; slides 14 and 16 added)_
* (06/10/21)
  [Higher-Order Types: F-omega](http://cambium.inria.fr/~remy/mpri/slides3.pdf)
  ([handout](http://cambium.inria.fr/~remy/mpri/handout3.pdf).
* (13/10/2021)
  [Logical relations](http://cambium.inria.fr/~remy/mpri/slides4.pdf)
  [(handout)](http://cambium.inria.fr/~remy/mpri/handout4.pdf);
  see also [chap 8](http://cambium.inria.fr/~remy/mpri/cours6.pdf)
  of [course notes](http://cambium.inria.fr/~remy/mpri/cours.pdf)).

You may also see [last year's schedule](http://cristal.inria.fr/~remy/mpri/2020/).

### Interpretation, Compilation, and Program Transformations (continued)

* (20/10/2021) Compiling away first-class functions:
  closure conversion, defunctionalization
  ([slides 03](slides/fpottier-03.pdf))
  ([Coq repo](coq/))
  (typed defunctionalization: [exercise](ocaml/pottier/foo.ml), [solution](ocaml/pottier/foo_defunctionalized.ml)).

* (27/10/2021) Making the stack explicit: the CPS transformation
  ([slides 04](slides/fpottier-04.pdf))
  ([Coq repo](coq/)).
  * Transforming a call-by-value interpreter
    ([exercise](ocaml/pottier/EvalCBVExercise.ml), [solution](ocaml/pottier/EvalCBVCPS.ml)).
  * Transforming a call-by-name interpreter
    ([solution](ocaml/pottier/EvalCBNCPS.ml)).
  * Transforming a graph traversal
    ([solution](ocaml/pottier/Graph.ml)).

* (03/11/2021) Some optimisations: constructor specialisation; stream fusion; staging
  ([slides 05](slides/fpottier-05.pdf)).
  * [Staging the power function](metaocaml/pottier/Power.ml).
  * [Staging stream fusion](metaocaml/pottier/StreamFusion.ml).
  * Running these examples requires MetaOCaml. Type `opam install 4.11.1+BER`.
    Then go down into `metaocaml/pottier` and type `make` and `make test`.

### Effects

* (10/11/2021)
  Paper discussion (1/3).
  Primitive effects vs. user-defined effects.
  Direct-style vs. indirect style.
* (17/11/2021)
  Monads in theory and practice.
  A continuum of algebraic structures: functors, monads, applicative functors.
* (8/12/2021)
  Effect handlers.
  Effects in proofs and logic.
* (15/12/2021)
  Paper discussion (2/3).
  Type systems for effects.

### Type-Directed Programming

These lectures will involve some hands-on experience and a fair bit of
improvisation. Perhaps not even in that order. To this end, it is
necessary to join the lecture with OCaml installed (say, at least
version 4.11.1).

* (05/01/2022)
  Algebraic programming
  ([OCaml warm-up](https://gitlab.com/pedagand/mpri-2.4-goto),
   [Categorical cheatsheet](slides/pedagand-00.pdf)).
* (12/01/2022)
  Algebraic programming (contd.)
  ([Coinduction](slides/pedagand-coinduction.pdf),
   [Agda source](agda/03-total/Recursion.lagda.rst)).
* (19/01/2022)
  Paper discussion (3/3).
  Generic programming
  ([Reading material](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf),
   [Source](agda/04-generic/Desc.lagda.rst)).
* (26/01/2022)
  Dependent functional programming
  ([OCaml warm-up](https://gitlab.com/pedagand/mpri-2.4-nbe),
   [Agda source](agda/02-dependent/Indexed.lagda.rst)
   [Agda online](https://nextjournal.com/pedagand/indexed-functional-programming)).


### Rust: programming with resources

* (02/02/2022)
* (09/02/2022)
* (16/02/2022)
* (23/02/2022)

## Evaluation of the course

Two written exams and one programming project are used to evaluate the
students.
By default, the mid-term and final exams will take place on
**01/12/2021** and **09/03/2022**, respectively.
Only course notes and hand-written notes are allowed for the exams.

Although the course has changed, you may still have a look at previous exams
available with solutions:

* intermediate exam 2020-2021:
  [Calcul d'objets](exams/intermediaire-2020-2021.pdf).
* mid-term exam 2020-2021:
  [Delimited control in System F](exams/partiel-2020-2021.pdf).
* final exam 2019-2020:
  [Gradually-typed functional languages](exams/final-2019-2020.pdf).
* mid-term exam 2019-2020:
  [A type system for information flow control](exams/partiel-2019-2020.pdf).
* final exam 2018-2019:
  (not available)
* mid-term exam 2018-2019:
  [A simple object encoding](exams/partiel-2018-2019.pdf).
* final exam 2017-2018:
  [Static differentiation](exams/final-2017-2018.pdf).
* mid-term exam 2017-2018:
  [Encoding call-by-name into call-by-value; extensible records](http://gallium.inria.fr/~remy/mpri/exams/partiel-2017-2018.pdf)
  ([Coq solution of part 1](coq/LambdaCalculusEncodingCBNIntoCBV.v)).

## Recommended software

Please install [opam](https://opam.ocaml.org/doc/Install.html) first.
A recent version is recommended (at the time of writing, 2.0.8).
If you have installed it already, skip this step.

Then, install OCaml 4.12.0,
[Coq 8.13.2](https://coq.inria.fr),
and
[AutoSubst](https://github.com/coq-community/autosubst) by executing
[this script](coq/installation.sh).
This script **does not destroy** your existing installation of
OCaml and Coq. It creates a new "switch" named `mpri24` and installs
appropriate versions of OCaml, Coq, and AutoSubst in it. You can activate
these versions with the following commands:

```bash
  ORIGINAL=$(opam switch show)
  opam switch mpri24
  eval "$(opam config env)"
```

and return to your original working environment with the following
command:

```bash
  opam switch "$ORIGINAL"
  eval "$(opam config env)"
```

In order to use Coq inside `emacs`,
[ProofGeneral](https://proofgeneral.github.io/)
is highly recommended.
Here is a suggested
[installation script](coq/proofgeneral.sh).

If desired, ProofGeneral can be further
[customized](https://proofgeneral.github.io/doc/userman/ProofGeneral_9/).

## Bibliography

[Types and Programming Languages](https://mitpress.mit.edu/books/types-and-programming-languages),
Benjamin C. Pierce, MIT Press, 2002.

[Advanced Topics in Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/attapl/),
edited by Benjamin C. Pierce, MIT Press, 2005.

[Practical Foundations for Programming Languages, Second Edition](http://www.cs.cmu.edu/~rwh/pfpl.html),
Robert Harper, Cambridge University Press, 2016.
