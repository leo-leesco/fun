# Functional programming and type systems (2022-2023)

This page supplements
[the official page of MPRI 2-4](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-4-2).

This course presents the principles, formalisms, and mathematical techniques
that underlie many of today's typed programming languages. Here are some
[introductory slides](slides/fpottier-00.pdf).

## Location and schedule

The lectures take place at University of Paris,
Bâtiment Sophie Germain, in room **1002**.

They are scheduled on **Wednesdays** from **9:00 to 11:45**.
There is a 15-minute break in the middle of each lecture,
so each lecture lasts 2h30.

## Content and teachers

* [Metatheory of typed programming languages](overview/remy.md)
  ([Didier Rémy](http://cambium.inria.fr/~remy/), *head*)
* [Interpretation, compilation, and program transformations](overview/pottier.md)
  ([François Pottier](http://cambium.inria.fr/~fpottier/))
* [Type-directed programming](overview/dagand.md)
  ([Pierre-Evariste Dagand](https://www.irif.fr/~dagand/))
* [Rust: programming safely with resources in a modern low-level programming
  language](overview/jourdan.md)
  ([Jacques-Henri Jourdan](https://jhjourdan.mketjh.fr/))
<!--
* [Effects](overview/scherer.md)
  ([Gabriel Scherer](http://www.lix.polytechnique.fr/Labo/Gabriel.Scherer/))
  -->

## Research Internship Proposals

We have posted the following internship proposals (possibly more to come):

* [Screaming fast symmetric cryptography](https://www.irif.fr/~dagand/stuffs/internship-2022-MPRI-usuba/usuba.pdf)
  (Pierre-Évariste Dagand);
* [Interopérabilité vérifiée entre OCaml et C](http://gallium.inria.fr/~agueneau/stages/camlffi.pdf)
  (Armaël Guéneau);
* [Type invariants and ghost code for deductive verification of Rust code](https://jhjourdan.mketjh.fr/pdf/StageGhostInvCreusot2023.pdf)
  (Jacques-Henri Jourdan);
* [Developing an Iris-Based Program Verification Framework for OCam](http://cambium.inria.fr/~fpottier/stages/sujet2023-m2.pdf)
  (Armaël Guéneau and François Pottier).

The internship offers posted by [the Prosecco team](https://team.inria.fr/prosecco/job-offers/) at Inria Paris are also relevant.

Please do not hesitate to talk to us (during the break or at the end of each lecture), to contact us by email, or to visit us at our offices.

See also [the official list of internship offers](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=internships) at MPRI.


## Time table

### <a name="interpretation">Interpretation, Compilation, and Program Transformations (introduction)

* (14/09/2022) Syntax, semantics, and interpreters.
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

### <a name="metatheory">Metatheory of Typed Programming Languages

* (21/09/2022)
  [Metatheory of System F](http://cambium.inria.fr/~remy/mpri/slides-metasf.pdf)
  [(handout)](http://cambium.inria.fr/~remy/mpri/handout-metasf.pdf);
  see chap [1,2,3](http://cambium.inria.fr/~remy/mpri/stlc.pdf)
  and [4](http://cambium.inria.fr/~remy/mpri/sf.pdf)
  of [course notes](http://cambium.inria.fr/~remy/mpri/cours-mpri.pdf)).
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
* (28/09/2022)
  [ADTs, existential types, GADTs](http://cambium.inria.fr/~remy/mpri/slides-exgadtA.pdf)
  ([handout](http://cambium.inria.fr/~remy/mpri/handout-exgadt.pdf)
   [without](http://cambium.inria.fr/~remy/mpri/handout-exgadtA.pdf) or
   [only](http://cambium.inria.fr/~remy/mpri/handout-exgadtB.pdf)
   the extra material);
  see also [chap 5](http://cambium.inria.fr/~remy/mpri/cours-exists.pdf)
   of [course notes](http://cambium.inria.fr/~remy/mpri/cours-mpri.pdf).
* (05/10/22)
  [Higher-Order Types: F-omega](http://cambium.inria.fr/~remy/mpri/slides-fomega.pdf)
  ([handout](http://cambium.inria.fr/~remy/mpri/handout-fomega.pdf));
  see also [chap 6](http://cambium.inria.fr/~remy/mpri/cours-fomega.pdf)
   of [course notes](http://cambium.inria.fr/~remy/mpri/cours-mpri.pdf).
* (12/10/2022)
  [Logical relations](http://cambium.inria.fr/~remy/mpri/slides-logrel.pdf)
  [(handout)](http://cambium.inria.fr/~remy/mpri/handout-logrel.pdf);
  see also [chap 7](http://cambium.inria.fr/~remy/mpri/cours-logical.pdf)
  of [course notes](http://cambium.inria.fr/~remy/mpri/cours-mpri.pdf).
* (19/10/2022)
  [Side Effects, References, Value restriction](http://cambium.inria.fr/~remy/mpri/slides-refval.pdf)
  [(handout)](http://cambium.inria.fr/~remy/mpri/handout-refval.pdf);
  see also [chap 3](http://cambium.inria.fr/~remy/mpri/cours-stlc)
  and [chap 4](http://cambium.inria.fr/~remy/mpri/cours-sf.pdf)
  of [course notes](http://cambium.inria.fr/~remy/mpri/cours-mpri.pdf).

You may also see [last year's
schedule](http://cristal.inria.fr/~remy/mpri/2021/) and lessons on
[type reconstruction](http://cambium.inria.fr/~remy/mpri/cours-inference.pdf)
[overloading](http://cambium.inria.fr/~remy/mpri/cours-overloading.pdf).



### <a name="transformation">Interpretation, Compilation, and Program Transformations (continuation)

* (26/10/2022) Compiling away first-class functions:
  closure conversion, defunctionalization
  ([slides 03](slides/fpottier-03.pdf))
  ([Coq repo](coq/))
  (typed defunctionalization: [exercise](ocaml/pottier/foo.ml), [solution](ocaml/pottier/foo_defunctionalized.ml)).

* (02/11/2022) Making the stack explicit: the CPS transformation
  ([slides 04](slides/fpottier-04.pdf))
  ([Coq repo](coq/)).
  * Transforming a call-by-value interpreter
    ([exercise](ocaml/pottier/EvalCBVExercise.ml), [solution](ocaml/pottier/EvalCBVCPS.ml)).
  * Transforming a call-by-name interpreter
    ([solution](ocaml/pottier/EvalCBNCPS.ml)).
  * Transforming a graph traversal
    ([solution](ocaml/pottier/Graph.ml)).

* (09/11/2022) Some optimisations: constructor specialisation; stream fusion; staging
  ([slides 05](slides/fpottier-05.pdf)).
  * [Staging the power function](metaocaml/pottier/Power.ml).
  * [Staging stream fusion](metaocaml/pottier/StreamFusion.ml).
  * Running these examples requires MetaOCaml. Type `opam switch create 4.11.1+BER --no-switch`.
    Then go down into `metaocaml/pottier` and type `make` and `make test`.

* (16/11/2022) System F in Coq (TODO).

<!--
### <a name="effects">Effects

Slides for the course: [slides.pdf](slides/scherer-2021.pdf).

* (09/11/2022).
  Primitive effects vs. user-defined effects.
  Direct-style vs. indirect style.
  Monads in theory and practice.
  [live code](ocaml/scherer/cours-2021-00.ml), [exercises](ocaml/scherer/exercises-2021-00.ml)
* (16/11/2022)
  Paper discussion (1/3): “Coordinated Concurrent Programming in Syndicate”, Tony Garnock-Jones and Matthias Felleisen, 2016
  A continuum of algebraic structures: functors, monads, applicative functors.
  [applicative-functors.md(slides/scherer-2021-applicative-functors.md)
* (7/12/2022)
  Effect handlers.
  Effects in proofs and logic.

  *Note*: due to the COVID situation, the December 8th lecture will be
  in *hybrid* format, available both on-premises and online (live) at
  the following URL:
  <https://greenlight.virtualdata.cloud.math.cnrs.fr/b/gab-2qz-ph2>

  You are completely free to choose either attendance format; in particular,
  please feel free to stay at home if you are at risk of COVID, or if
  you are in any way stressed by the idea of attending the lecture in
  person.

* (14/12/2022)
  Paper discussion (2/3).
  Type systems for effects.

-->

### <a name="type">Type-Directed Programming

These lectures will involve some hands-on experience and a fair bit of
improvisation. Perhaps not even in that order. To this end, it is
necessary to join the lecture with OCaml installed (say, at least
version 4.11.1).

Online presence: https://webconf.math.cnrs.fr/b/dag-ddd-p4n

* (07/12/2022)
* (14/12/2023)
  Overloading ([handout](http://cambium.inria.fr/~remy/mpri/cours-overloading.pdf))
* (04/01/2023)
  GADTs & type inference ([handout](http://cambium.inria.fr/~remy/mpri/cours-inference.pdf))
* (11/01/2023)
  Dependent functional programming
  ([OCaml warm-up](https://gitlab.com/pedagand/mpri-2.4-nbe-2022),
   [Agda source](agda/02-dependent/Indexed.lagda.rst)
   [Agda online](https://nextjournal.com/pedagand/indexed-functional-programming)).
* (18/01/2023)
  Paper discussion (3/3).
  Generic programming
  ([Reading material](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf),
   [Source](agda/04-generic/Desc.lagda.rst)).


### <a name="rust">Rust: programming with resources

Lectures:
* (25/01/2023) Introduction to Rust programming ([slides](slides/jhjourdan-01.pdf)).
* (01/02/2023) Introduction to unsafe Rust and interrior mutability ([slides](slides/jhjourdan-02.pdf)), and hands-on session ([exercises](tdtp/jhjourdan1.pdf), [solution](tdtp/jhjourdan1_solution.rs)).
* (08/02/2023) Rust and multithreading ([slides](slides/jhjourdan-03.pdf)), and hands-on session ([exercises](tdtp/jhjourdan2.pdf), [template](tdtp/jhjourdan2_template.rs), [solution](tdtp/jhjourdan2_solution.rs)).
* (15/02/2023) Formalizing Rust's type system ([slides](slides/jhjourdan-04.pdf)).
* (22/02/2023) TODO.

In order to participate to the hands-on exercises of these lectures, the students should install on their computer the following tools:
* The Rust compiler, version at least 1.41
* The Cargo package manager, any compatible version
Installing these tools should be easy on any recent Linux distribution using the system's package manager. Alternatively, students can follow the instructions at the following URL: https://rustup.rs/

In order to test the installation, the students are asked to use the Rust compiler on the following program:
```
fn main() {
  let mut f = |x : i32| x;
  let _r : &mut dyn Fn(i32) -> i32 = &mut f;
  println!("{}", f(42))
}
```
If the compiler is correctly installed, then the command `rustc test.rs` should produce an executable.

Physical presence at the lectures is required, when possible. If the COVID situation makes this impossible, students can follow the course using the following URL: https://webconf.math.cnrs.fr/b/jou-gaq-9gr

## Evaluation of the course

Two written exams and one programming project are used to evaluate the
students.

The mid-term and final exams are expected to take place on
**30/11/2022** and **08/03/2023**.
Only course notes and hand-written notes are allowed for the exams.

Although the course has changed, you may still have a look at previous exams
available with solutions:

* final exam 2021-2022:
  [type class elaboration](exams/final-2021-2022.pdf).
* mid-term exam 2021-2022:
  [gradual typing](exams/partiel-2021-2022.pdf).
* intermediate exam 2020-2021:
  [calcul d'objets](exams/intermediaire-2020-2021.pdf).
* mid-term exam 2020-2021:
  [delimited control in System F](exams/partiel-2020-2021.pdf).
* final exam 2019-2020:
  [gradually-typed functional languages](exams/final-2019-2020.pdf).
* mid-term exam 2019-2020:
  [a type system for information flow control](exams/partiel-2019-2020.pdf).
* final exam 2018-2019:
  (not available)
* mid-term exam 2018-2019:
  [a simple object encoding](exams/partiel-2018-2019.pdf).
* final exam 2017-2018:
  [static differentiation](exams/final-2017-2018.pdf).
* mid-term exam 2017-2018:
  [encoding call-by-name into call-by-value; extensible records](http://gallium.inria.fr/~remy/mpri/exams/partiel-2017-2018.pdf)
  ([Coq solution of part 1](coq/LambdaCalculusEncodingCBNIntoCBV.v)).

## <a name="project">Programming Project</a>

Programming is an important part of the course. We give a mandatory
programming project (around the end of October) which must be completed
roughly by the end of January. The programming project counts for about a
third of the final grade.

<!--
The [programming project](project/2022-2023/) is now available.
Read the [assignment](project/2022-2023/sujet.pdf).

The deadline for submitting your project is **XXX**.

Please do not hesitate to ask questions about the project,
of an administrative or technical nature,
to [François Pottier](francois.pottier@inria.fr).
-->

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
