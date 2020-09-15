# Functional programming and type systems (2020-2021)

This page supplements
[the official page of MPRI 2-4](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-4-2).

## Location and duration

The lectures take place at University of Paris,
Bâtiment Sophie Germain, in room **1013**.

They are scheduled on **Wednesdays** from 12:45 to 15:30.
There is a 15-minute break in the middle of each lecture.

## Teachers

* Functional Programming: Under the Hood
  (6 installments, [François Pottier](http://cambium.inria.fr/~fpottier))
* Metatheory of Typed Programming Languages
  (7 installements, [Didier Rémy](http://cambium.inria.fr/~remy/), *head*)
* Dependently-typed Functional Programming
  (7 installments, [Pierre-Evariste Dagand](https://pages.lip6.fr/Pierre-Evariste.Dagand/))

## Aims

This course presents the principles and formalisms that underlie many of
today's typed functional programming languages.
(Here are some [introductory slides](slides/fpottier-00.pdf).)

This year, the course is made up of three parts and cannot be split.

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
reasoning by induction on the structure of types.  Finally, we introduce
subtyping, row polymorphism, and illustrate the problems induced by
side effects (references) and the need for the value restriction.

The last part focuses on the use of dependent types for programming:
effectful programming with monads and algebraic effects; tagless
interpreters; programming with total functions; generic programming.
We also show the limits of dependently-typed functional programming.

## Programming Project

A programming project will be made available somewhere near the middle
of the course.

## Research internship proposals

No internship proposals have been posted by us this year yet.

Please do not hesitate to talk to us (during the break or at the end of each lecture),
to contact us by email,
or to visit us at our offices.

## Approximate syllabus

### Functional Programming: Under the Hood

* (16/09/2020)
  * Introduction
      ([slides 00](slides/fpottier-00.pdf)).
  * Syntax and operational semantics, on paper
      ([slides 01a](slides/fpottier-01a.pdf)).
  * Syntax, on a machine
      ([slides 01b](slides/fpottier-01b.pdf)).
* (23/09/2020)
  * Operational semantics, on a machine
      ([Coq demo](coq/DemoSyntaxReduction.v)).
  * From a small-step semantics down to an efficient verified interpreter,
    in several stages
      ([slides 02](slides/fpottier-02.pdf))
      ([the lambda-calculus in OCaml](ocaml/pottier/Lambda.ml))
      ([Coq repo](coq/)).
* (30/09/2020) Compiling away first-class functions:
  closure conversion, defunctionalization
  ([slides 03](slides/fpottier-03.pdf))
  ([Coq repo](coq/)).
* (07/10/2020) Making the stack explicit: the CPS transformation
  ([slides 04](slides/fpottier-04.pdf))
  ([Coq repo](coq/)).
  * Transforming a call-by-value interpreter
    ([exercise](ocaml/pottier/EvalCBVExercise.ml), [solution](ocaml/pottier/EvalCBVCPS.ml)).
  * Transforming a call-by-name interpreter
    ([solution](ocaml/pottier/EvalCBNCPS.ml)).
  * Transforming a graph traversal
    ([solution](ocaml/pottier/Graph.ml)).
* (14/10/2020) Equational reasoning and program optimizations
  ([slides 05](slides/fpottier-05.pdf))
  ([Coq mini-demo](coq/DemoEqReasoning.v)).

### Metatheory of Typed Programming Languages

* (21/10/2020)
  [Metatheory of System F](http://gallium.inria.fr/~remy/mpri/slides1.pdf)
  [(handout)](http://gallium.inria.fr/~remy/mpri/handout1.pdf)
  (see also [intro](http://gallium.inria.fr/~remy/mpri/slides8.pdf),
  and chap [1,2,3](http://gallium.inria.fr/~remy/mpri/cours1.pdf)
  and [4](http://gallium.inria.fr/~remy/mpri/cours2.pdf)
  of [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf))
* (28/10/2020)
  [ADTs, existential types, GADTs](http://gallium.inria.fr/~remy/mpri/slides2.pdf)
  ([handout](http://gallium.inria.fr/~remy/mpri/handout2.pdf)
   [without](http://gallium.inria.fr/~remy/mpri/handout2a.pdf) or
   [only](http://gallium.inria.fr/~remy/mpri/handout2b.pdf)
   the extra material)
  (see also [chap 6](http://gallium.inria.fr/~remy/mpri/cours4.pdf)
   of [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf))
* (04/11/2020?)
  [References, Value restriction, Side effects](http://gallium.inria.fr/~remy/mpri/slides5.pdf)
  ([handout](http://gallium.inria.fr/~remy/mpri/handout5.pdf))
  (see also sections [3.6, 3.7](http://gallium.inria.fr/~remy/mpri/cours1.pdf)
   and [4.5](http://gallium.inria.fr/~remy/mpri/cours2.pdf)
   of [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf))
* (25/11/2020?)
  [Logical relations](http://gallium.inria.fr/~remy/mpri/slides3.pdf)
  [(handout)](http://gallium.inria.fr/~remy/mpri/handout3.pdf)
  ([chap 8](http://gallium.inria.fr/~remy/mpri/cours6.pdf)
   of [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf))
* (02/12/2020?)
  [Overloading](http://gallium.inria.fr/~remy/mpri/slides4.pdf)
  [(handout)](http://gallium.inria.fr/~remy/mpri/handout4.pdf)
  (see also [chap 7](http://gallium.inria.fr/~remy/mpri/cours5.pdf)
  of [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf))
* See exercises in [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf)

### Dependently-typed Functional Programming

These lectures will involve some hands-on experience. To this end, it is
necessary to bring a laptop on which Agda (version 2.6.0.1 or higher)
is installed. A quick installation guide as well as further pointers
can be found [here](agda/00-agda/Warmup.lagda.rst).

* [Guidelines](agda/Index.lagda.rst)
* (09/12/2020?) Introduction & Setup
  ([Source](agda/00-agda/Warmup.lagda.rst),
   [categorical cheatsheet](slides/pedagand-00.pdf),
   [McCompiler.v](coq/McCompiler.v))
* (16/12/2020?)
  [Effectful functional programming](slides/pedagand-01.pdf)
  ([Source](agda/01-effectful/Monad.lagda.rst)).
* (06/01/2021?)
  [Dependent functional programming](slides/pedagand-02.pdf)
  ([Source](agda/02-dependent/Indexed.lagda.rst)).
* (13/01/2021?)
  [Total functional programming](slides/pedagand-03.pdf)
  ([Source](agda/03-total/Recursion.lagda.rst)).
* (20/01/2021?)
  [Generic functional programming](slides/pedagand-04.pdf)
  ([Source](agda/04-generic/Desc.lagda.rst)) &
  [Open problems in dependent functional programming](slides/pedagand-05.pdf)
  ([Source](agda/05-open/Problems.lagda.rst)).

## Evaluation of the course

Two written exams and one programming project are used to evaluate the
students who follow the full course. Only the mid-term exam is used to
grade students who choose to split the course.

The mid-term exam wil ltake place on (to be determined).
The final exam will take place on (to be determined).

Only course notes and hand-written notes are allowed for the exams.

Although the course has changed, you may still have a look at previous exams
available with solutions:

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
* mid-term exam 2016-2017:
  [Record concatenation](http://gallium.inria.fr/~remy/mpri/exams/partiel-2016-2017.pdf).
* mid-term exam 2015-2016:
  [Type containment](http://gallium.inria.fr/~remy/mpri/exams/partiel-2015-2016.pdf).
* final exam 2014-2015:
  [Copatterns](http://gallium.inria.fr/~remy/mpri/exams/final-2014-2015.pdf).
* mid-term exam 2014-2015:
  [Information flow](http://gallium.inria.fr/~remy/mpri/exams/partiel-2014-2015.pdf).
* final exam 2013-2014:
  [Operations on records](http://gallium.inria.fr/~remy/mpri/exams/final-2013-2014.pdf).
* mid-term exam 2013-2014:
  [Typechecking effects](http://gallium.inria.fr/~remy/mpri/exams/partiel-2013-2014.pdf).
* final exam 2012-2013:
  [Refinement types](http://gallium.inria.fr/~remy/mpri/exams/final-2012-2013.pdf).
* mid-term exam 2012-2013:
  [Variations on ML](http://gallium.inria.fr/~remy/mpri/exams/partiel-2012-2013.pdf).
* final exam  2011-2012:
  [Intersection types](http://gallium.inria.fr/~remy/mpri/exams/final-2011-2012.pdf).
* mid-term exam  2011-2012:
  [Parametricity](http://gallium.inria.fr/~remy/mpri/exams/partiel-2011-2012.pdf).
* final exam 2010-2011:
  [Compiling a language with subtyping](http://gallium.inria.fr/~xleroy/mpri/2-4/exam-2010-2011.pdf).
* mid-term exam 2010-2011:
  [Compilation of polymorphic records](http://gallium.inria.fr/~remy/mpri/exams/partiel-2010-2011.pdf).

## Recommended software

Please install [opam](https://opam.ocaml.org/doc/Install.html) first.
A recent version is recommended (at the time of writing, 2.0.5).
If you have installed it already, skip this step.

Then, install OCaml 4.0x, Coq **8.5.3** and AutoSubst by executing
[this script](coq/installation.sh).
This script **does not destroy** your existing installation of
OCaml and Coq. It creates a new "switch" named `mpri24` and installs
appropriate versions of OCaml, Coq, and AutoSubst in it. You can activate
these versions with the following commands:

```bash
  opam switch mpri24
  eval `opam config env`
```

and return to your usual version of OCaml (say, 4.07.0) with the following commands:

```bash
  opam switch 4.07.0
  eval `opam config env`
```

In order to use Coq inside `emacs`,
[ProofGeneral](https://proofgeneral.github.io/)
is highly recommended.
Here is a suggested
[installation script](coq/proofgeneral.sh).

If desired, ProofGeneral can be further
[customized](https://proofgeneral.github.io/doc/userman/ProofGeneral_9/).

To install and familiarize yourself with Agda, please follow the
[instructions](agda/00-agda/Warmup.lagda.rst).

## Bibliography

[Types and Programming Languages](https://mitpress.mit.edu/books/types-and-programming-languages),
Benjamin C. Pierce, MIT Press, 2002.

[Advanced Topics in Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/attapl/),
edited by Benjamin C. Pierce, MIT Press, 2005.

[Practical Foundations for Programming Languages, Second Edition](http://www.cs.cmu.edu/~rwh/pfpl.html),
Robert Harper, Cambridge University Press, 2016.
