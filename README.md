# Functional programming and type systems (2018-2019)

This page supplements
[the official page of MPRI 2-4](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-4-2).

## Location and duration

The lectures take place at University Paris 7 - Denis Diderot,
Bâtiment Sophie Germain, in room 2035.

They are scheduled on Fridays from 12:45 to 15:30.
There is a 15-minute break in the middle of each lecture.

## Teachers

   * Functional Programming: Under the Hood (12h30, [François Pottier](http://gallium.inria.fr/~fpottier))
   * Metatheory of Typed Programming Languages (12h30, [Didier Rémy](http://gallium.inria.fr/~remy/), *head*)
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

The third part of the course introduces "rich" type systems designed
to guarantee extra properties in addition to safety: principality,
information hiding, modularity, extensionality, purity, control of
effects, algorithmic invariants, complexity, resource usage, or full
functional correctness. The expressivity of these systems sometimes
endangers the tractability, or even the feasibility, of type checking
and type inference: a common thread between these lectures discusses
the tradeoffs made on the design of these systems to balance
expressivity and tractability.

The last part focuses on the use of dependent types for programming:
effectful programming with monads and algebraic effects; tagless
interpreters; programming with total functions; generic programming.
We also show the limits of dependently-typed functional programming.

## Project

The programming project is not yet available.

## Approximate syllabus

### Functional Programming: Under the Hood

* (14/09/2018)
  Introduction ([slides 00](slides/fpottier-00.pdf)).
  Syntax and operational semantics, on paper and on a machine
  ([slides 01a](slides/fpottier-01a.pdf))
  ([slides 01b](slides/fpottier-01b.pdf)).
  * Newton-Raphson in OCaml ([solution](ocaml/NewtonRaphson.ml)).
  * 1 is not even in Coq ([Even.v](coq/Even.v)).
* (21/09/2018)
  From a small-step semantics down to an efficient verified interpreter,
  in several stages
  ([Coq demo](coq/DemoSyntaxReduction.v))
  ([slides 02](slides/fpottier-02.pdf))
  ([OCaml code](ocaml/Lambda.ml))
  ([Coq repo](coq/)).
* (28/09/2018) Compiling away first-class functions:
  closure conversion, defunctionalization
  ([slides 03](slides/fpottier-03.pdf))
  ([Coq repo](coq/)).
* (05/10/2018) Making the stack explicit: the CPS transformation
  ([slides 04](slides/fpottier-04.pdf))
  ([Coq repo](coq/)).
  * Transforming a call-by-value interpreter
    ([exercise](ocaml/EvalCBVExercise.ml), [solution](ocaml/EvalCBVCPS.ml)).
  * Transforming a call-by-name interpreter
    ([solution](ocaml/EvalCBNCPS.ml)).
  * Transforming a graph traversal
    ([solution](ocaml/Graph.ml)).
* (12/10/2018) Equational reasoning and program optimizations
  ([slides 05](slides/fpottier-05.pdf))
  ([Coq mini-demo](coq/DemoEqReasoning.v)).

### Metatheory of Typed Programming Languages

* (19/10/2018)
  [Metatheory of System F](http://gallium.inria.fr/~remy/mpri/slides1.pdf)
  [(handout)](http://gallium.inria.fr/~remy/mpri/handout1.pdf)
  (see also [intro](http://gallium.inria.fr/~remy/mpri/slides8.pdf),
  and chap [1,2,3](http://gallium.inria.fr/~remy/mpri/cours1.pdf)
  and [4](http://gallium.inria.fr/~remy/mpri/cours2.pdf)
  of [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf))
* (26/10/2018)
  [ADTs, existential types, GADTs](http://gallium.inria.fr/~remy/mpri/slides2.pdf)
  ([handout](http://gallium.inria.fr/~remy/mpri/handout2.pdf)
   [without](http://gallium.inria.fr/~remy/mpri/handout2a.pdf) or
   [only](http://gallium.inria.fr/~remy/mpri/handout2b.pdf)
   the extra material)
  (se also [chap 6](http://gallium.inria.fr/~remy/mpri/cours4.pdf)
   of [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf))
* (02/11/2018)
  [Logical relations](http://gallium.inria.fr/~remy/mpri/slides3.pdf)
  [(handout)](http://gallium.inria.fr/~remy/mpri/handout3.pdf)
  ([chap 8](http://gallium.inria.fr/~remy/mpri/cours6.pdf)
   of [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf))
* (09/11/2018) ~~Subtyping. Rows.~~
  [Overloading](http://gallium.inria.fr/~remy/mpri/slides4.pdf)
  [(handout)](http://gallium.inria.fr/~remy/mpri/handout4.pdf)
  (see also [chap 7](http://gallium.inria.fr/~remy/mpri/cours5.pdf)
  of [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf))
* (16/11/2018)
  [References, Value restriction, Side effects](http://gallium.inria.fr/~remy/mpri/slides5.pdf)
  ([handout](http://gallium.inria.fr/~remy/mpri/handout5.pdf))
  (see also sections [3.6, 3.7](http://gallium.inria.fr/~remy/mpri/cours1.pdf)
   and [4.5](http://gallium.inria.fr/~remy/mpri/cours2.pdf)
   of [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf))
* See exercises in [course notes](http://gallium.inria.fr/~remy/mpri/cours.pdf)


### Rich types, tractable typing

(07/12/2018) (14/12/2018) (21/12/2018) (11/01/2019) (18/01/2019)

* [Introduction](slides/yrg-00-introduction.pdf),
  [ML and Type inference](slides/yrg-01-type-inference.pdf)
* (15/12/2017) Subtyping
  [Exercises](slides/yrg-02-diy-lambda-calculus-with-subtyping.pdf)
  [Answers](slides/yrg-03-diy-lambda-calculus-with-subtyping-answers.pdf)
* (22/12/2017 - 12/01/2018) Dependent types
  [GADTs](slides/yrg-04-gadt-metatheory.pdf),
  [Exercises](slides/yrg-05-diy-lambda-pi.pdf)
* (19/01/2018) [Functional correctness](slides/yrg-06-functional-correctness.pdf)
* Effects and resources

### Dependently-typed Functional Programming

(25/01/2019) (/01/02/2019) (08/02/2019) (15/02/2019) (22/02/2019)

* [Guidelines](agda/Index.lagda.rst)
* [Effectful functional programming](slides/pedagand-01.pdf) ([Source](agda/01-effectful/Monad.lagda.rst)).
* [Dependent functional programming](slides/pedagand-02.pdf) ([Source](agda/02-dependent/Indexed.lagda.rst), [McCompiler.v](coq/McCompiler.v)).
* [Total functional programming](slides/pedagand-03.pdf) ([Source](agda/03-total/Recursion.lagda.rst)).
* [Generic functional programming](slides/pedagand-04.pdf) ([Source](agda/04-generic/Desc.lagda.rst)).
* [Open problems in dependent functional programming](slides/pedagand-05.pdf) ([Source](agda/05-open/Problems.lagda.rst)).

## Evaluation of the course

Two written exams (a partial exam on Friday Nov 23 or 30 and a final exam on
March 1 or 8) and one programming project or several programming exercises
are used to evaluate the students that follow the full course. Only the
partial exam will count to grade students who split the course.

Only course notes and hand written notes are allowed for the exams.

Although the course has changed, you may still have a look at previous exams
available with solutions:

- mid-term exam 2017-2018:
  [Encoding call-by-name into call-by-value; extensible records](http://gallium.inria.fr/~remy/mpri/exams/partiel-2017-2018.pdf)
  ([Coq solution of part 1](coq/LambdaCalculusEncodingCBNIntoCBV.v)).
- mid-term exam 2016-2017:
  [Record concatenation](http://gallium.inria.fr/~remy/mpri/exams/partiel-2016-2017.pdf).
- mid-term exam 2015-2016:
  [Type containment](http://gallium.inria.fr/~remy/mpri/exams/partiel-2015-2016.pdf).
- final exam 2014-2015:
  [Copatterns](http://gallium.inria.fr/~remy/mpri/exams/final-2014-2015.pdf).
- mid-term exam 2014-2015:
  [Information flow](http://gallium.inria.fr/~remy/mpri/exams/partiel-2014-2015.pdf).
- final exam 2013-2014:
  [Operations on records](http://gallium.inria.fr/~remy/mpri/exams/final-2013-2014.pdf).
- mid-term exam 2013-2014:
  [Typechecking effects](http://gallium.inria.fr/~remy/mpri/exams/partiel-2013-2014.pdf).
- final exam 2012-2013:
  [Refinement types](http://gallium.inria.fr/~remy/mpri/exams/final-2012-2013.pdf).
- mid-term exam 2012-2013:
  [Variations on ML](http://gallium.inria.fr/~remy/mpri/exams/partiel-2012-2013.pdf).
- final exam  2011-2012:
  [Intersection types](http://gallium.inria.fr/~remy/mpri/exams/final-2011-2012.pdf).
- mid-term exam  2011-2012:
  [Parametricity](http://gallium.inria.fr/~remy/mpri/exams/partiel-2011-2012.pdf).
- final exam 2010-2011:
  [Compiling a language with subtyping](http://gallium.inria.fr/~xleroy/mpri/2-4/exam-2010-2011.pdf).
- mid-term exam 2010-2011:
  [Compilation of polymorphic records](http://gallium.inria.fr/~remy/mpri/exams/partiel-2010-2011.pdf).

## Recommended software

Please install [opam](https://opam.ocaml.org/doc/Install.html) first.

Then, install OCaml 4.0x and Coq **8.5** via the following commands:
```bash
opam init --comp=4.05 # for instance
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install -j4 -v coq.8.5.3
```
(Do *not* install Coq 8.6. The version of AutoSubst that I am using is
not compatible with it. If for some reason you need Coq 8.6, or have
already installed Coq 8.6, note that `opam switch` can be used to let
multiple versions of Coq coexist.)

Please also install François Pottier's
[variant](https://github.com/fpottier/autosubst)
of the
[AutoSubst](https://www.ps.uni-saarland.de/autosubst/) library:
```bash
git clone git@github.com:fpottier/autosubst.git
make -C autosubst install
```

In order to use Coq inside `emacs`,
[ProofGeneral](https://proofgeneral.github.io/)
is highly recommended.
Here is a suggested installation script:
```bash
rm -rf /tmp/PG
cd /tmp
git clone git@github.com:ProofGeneral/PG.git
cd PG
EMACS=/Applications/Aquamacs.app/Contents/MacOS/Aquamacs
if [ ! -x $EMACS ]; then
  EMACS=emacs
fi
make EMACS=$EMACS compile
TARGET=/usr/local/share/emacs/site-lisp/ProofGeneral
sudo rm -rf $TARGET
sudo mv /tmp/PG $TARGET
```

Enable ProofGeneral by adding the following line to your `.emacs` file:
```elisp
(load-file "/usr/local/share/emacs/site-lisp/ProofGeneral/generic/proof-site.el")
```
If desired, ProofGeneral can be further
[customized](https://proofgeneral.github.io/doc/userman/ProofGeneral_9/).

To install and familiarize yourself with Agda, please follow the
[instructions](agda/00-agda/Warmup.lagda.rst).

## Bibliography

[Types and Programming Languages](https://mitpress.mit.edu/books/types-and-programming-languages),
Benjamin C. Pierce, MIT Press, 2002.

[Advanced Topics in Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/attapl/),
Edited by Benjamin C. Pierce, MIT Press, 2005.
