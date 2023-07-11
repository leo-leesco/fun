## Time table (2022-2023)

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

* (16/11/2022) A (slow) walk through the garden of type soundness proofs,
  in Coq ([Coq repo](coq/), [html](coq/html/)).

  We will work first on simply-typed lambda-calculus ([blank file](coq/STLCTypeSoundnessBlank.v)),
  then on System F in Curry style ([blank file](coq/SystemFTypeSoundnessBlank.v)).
  Curry style means that type abstractions and type applications are implicit;
  this is in contrast with Church style, where they are explicit in the syntax of terms.

  To view the definitions, lemmas, and solutions online, please use the following links:
  - Lambda-calculus:
    [syntax](http://cambium.inria.fr/~fpottier/mpri/html/LambdaCalculusSyntax.html),
    [values](http://cambium.inria.fr/~fpottier/mpri/html/LambdaCalculusValues.html),
    [reduction](http://cambium.inria.fr/~fpottier/mpri/html/LambdaCalculusReduction.html).
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

### <a name="type">Type-Directed Programming

These lectures will involve some hands-on experience and a fair bit of
improvisation. Perhaps not even in that order. To this end, it is
necessary to join the lecture with OCaml installed (say, at least
version 4.11.1).


* (07/12/2023)
  Overloading ([handout](http://cambium.inria.fr/~remy/mpri/cours-overloading.pdf))
* **[{ Bring Your Own Laptop }]** (14/12/2022)
  Monads ([OCaml warm-up](https://gitlab.com/pedagand/mpri-2.4-monads-2023),
          [Agda source](agda/01-effectful/Monad.lagda.rst))
* (04/01/2023)
  Bidirectional type-checking
*  **[{ Bring Your Own Laptop }]** (11/01/2023)
  Dependent functional programming
  ([OCaml warm-up](https://gitlab.com/pedagand/mpri-2.4-nbe-2023),
   [Agda source](agda/02-dependent/Indexed.lagda.rst)).
* (18/01/2023)
  Generic programming
  ([Reading material](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf),
   [Source](agda/04-generic/Desc.lagda.rst)).


### <a name="rust">Rust: programming with resources

Lectures:
* (25/01/2023) Introduction to Rust programming ([slides](slides/jhjourdan-01.pdf)).
* (01/02/2023) Rust: When the Aliasing Discipline Is Too Strong ([slides](slides/jhjourdan-02.pdf)).
* (08/02/2023) Rust and Multithreading ([slides](slides/jhjourdan-03.pdf)).
* (15/02/2023) Formalizing Rust's Type System ([slides](slides/jhjourdan-04.pdf)).
* (22/02/2023) Formalizing Rust's Type System (part 2) ([slides](slides/jhjourdan-04.pdf)).

Hands-on:
* (01/02/2023) Introduction to Rust ([exercises](tdtp/jhjourdan1.pdf), [solution](tdtp/jhjourdan1_solution.rs)).
* (15/02/2023) Interior Mutability and Concurrency ([exercises](tdtp/jhjourdan2.pdf), [template](tdtp/jhjourdan2_template.rs), [solution](tdtp/jhjourdan2_solution.rs)).
* (22/02/2023) Logical Relations for Type Systems Safety ([exercises](tdtp/jhjourdan3.pdf)).

### <a name="effects">Effects (2021-2022)

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
