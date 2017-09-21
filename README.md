# Functional programming and type systems (2017-2018)

This page supplements
[the official page of MPRI 2-4](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-4-2).

## Location and duration

The lectures take place at University Paris 7 - Denis Diderot,
Bâtiment Sophie Germain, in room 2035.

They are scheduled on Fridays from 12:45 to 15:30.
There is a 15-minute break in the middle of each lecture.

## Teachers

   * Functional Programming: Under the Hood (12h30, [François Pottier](http://gallium.inria.fr/~fpottier))
   * [Metatheory of Typed Programming Languages](http://gallium.inria.fr/~remy/mpri/) (12h30, [Didier Rémy](http://gallium.inria.fr/~remy/), *head*)
   * Advanced Aspects of Type Systems (12h30, [Yann Régis Gianas](http://www.pps.jussieu.fr/~yrg/))
   * Dependently-typed Functional Programming (12h30, [Pierre-Evariste Dagand](https://pages.lip6.fr/Pierre-Evariste.Dagand/))

## Aims

This course presents the principles and formalisms that underlie many of
today's typed functional programming languages.
(Here are some [introductory slides](slides/fpottier-00.pdf).)

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
reasoning by induction on the structure of types.  Finally, we introduce
subtyping, row polymorphism, and illustrate the problems induced by
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

* (15/09/2017)
  [Metatheory of System F](http://gallium.inria.fr/~remy/mpri/slides1.pdf)
  (See also [intro](http://gallium.inria.fr/~remy/mpri/slides8.pdf),
  and chap [1](http://gallium.inria.fr/~remy/mpri/cours1.pdf)
  and [2](http://gallium.inria.fr/~remy/mpri/cours2.pdf)
  of [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf))
* (27/10/2017) ADTs, existential types, GADTs.
* (03/11/2017) Logical relations.
* (10/11/2017) Subtyping. Rows.
* (17/11/2017) References, Value restriction, Side effects.

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

## Evaluation of the course

Two written exams (a partial and a final exam) and one programming project
or several programming exercises are used to evaluate the students that
follow the full course.  Only the partial exam will count to grade students
who split the course.

Although the course has changed, you may still have a look at previous exams
available with solutions:

- mid-term exam 2016-2017:
 [Record concatenation](http://gallium.inria.fr/~remy/mpri/exams/partiel-2016-2017.pdf)
- mid-term exam 2015-2016:
 [Type containment](http://gallium.inria.fr/~remy/mpri/exams/partiel-2015-2016.pdf)
- final exam 2014-2015: [Copatterns](http://gallium.inria.fr/~remy/mpri/exams/final-2014-2015.pdf)
- mid-term exam 2014-2015:
 [Information flow](http://gallium.inria.fr/~remy/mpri/exams/partiel-2014-2015.pdf)
- final exam 2013-2014:
 [Operation on records](http://gallium.inria.fr/~remy/mpri/exams/final-2013-2014.pdf)
- mid-term exam 2013-2014:
 [Typechecking Effects](http://gallium.inria.fr/~remy/mpri/exams/partiel-2013-2014.pdf)
- final exam 2012-2013:
 [Refinement types](http://gallium.inria.fr/~remy/mpri/exams/final-2012-2013.pdf)
- mid-term exam 2012-2013:
 [Variations on ML](http://gallium.inria.fr/~remy/mpri/exams/partiel-2012-2013.pdf)
- final exam  2011-2012:
 [Intersection types](http://gallium.inria.fr/~remy/mpri/exams/final-2011-2012.pdf)
- mid-term exam  2011-2012:
 [Parametricity](http://gallium.inria.fr/~remy/mpri/exams/partiel-2011-2012.pdf)
- final exam 2010-2011:
  [Compiling a language with subtyping](http://gallium.inria.fr/~xleroy/mpri/2-4/exam-2010-2011.pdf)
- mid-term exam 2010-2011:
 [Compilation
 of polymorphic records](http://gallium.inria.fr/~remy/mpri/exams/2010/partiel-2010-2011.pdf)

## Recommended software

OCaml 4.0x and Coq **8.5**.

Once you have installed [opam](https://opam.ocaml.org/doc/Install.html), use the following commands:
```bash
opam init --comp=4.05 # for instance
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install -j4 -v coq.8.5.3
```

Please also install François Pottier's
[variant](https://github.com/fpottier/autosubst)
of the
[AutoSubst](https://www.ps.uni-saarland.de/autosubst/) library:
```bash
git clone git@github.com:fpottier/autosubst.git
make -C autosubst install
```

## Bibliography

[Types and Programming Languages](https://mitpress.mit.edu/books/types-and-programming-languages),
Benjamin C. Pierce, MIT Press, 2002.

[Advanced Topics in Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/attapl/),
Edited by Benjamin C. Pierce, MIT Press, 2005.
