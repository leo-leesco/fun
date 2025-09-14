# Functional programming and type systems (FUN) (2025-2026)

This is the main home page
of the course *Functional programming and type systems*,
also known under the code names *2.4* and *FUN*.
The course also has a shorter
[official page](https://mpri-master.ens.fr/doku.php?id=cours:fun) on MPRI's site.

This course presents the principles, formalisms, and mathematical techniques
that underlie many of today's typed programming languages, including OCaml,
Haskell, and Rust.
Here are some [introductory slides](slides/fpottier-00.pdf).

The course is taught by
[Jacques-Henri Jourdan](https://jhjourdan.mketjh.fr/) (JHJ),
[François Pottier](http://cambium.inria.fr/~fpottier/) (FP)
(*head*),
[Gabriel Scherer](http://www.lix.polytechnique.fr/Labo/Gabriel.Scherer/) (GS),
and
[Yannick Zakowski](https://cambium.inria.fr/~yzakowsk/) (YZ).
This year,
one lecture will be given by Didier Rémy (DR).

The content of the course is partly renewed in 2025-2026.
In particular,
we will go deeper into monads,
with two new lectures on **interaction trees**
and **modular monadic semantics**
for programming languages.
Also, the last part of the course includes
a new lecture on
**translating Rust to purely functional code**.

Didier Rémy's [slides and lecture notes](http://cristal.inria.fr/~remy/mpri/),
from an earlier version of the course,
are still available and can serve as a useful reference.

## Location and Schedule

The lectures take place at University of Paris,
Bâtiment Sophie Germain,
in room **1004**.

They are scheduled on **Wednesdays** from **12:45** to **15:30**.
There is a 15-minute break in the middle of each lecture,
so each lecture lasts 2h30.

## Syllabus and Time Table

The syllabus is organized in four main segments of roughly comparable sizes.
The title of each segment (below) is a hyperlink;
click it to obtain a more detailed description of each segment.

### [Syntax, Operational Semantics, and Type Systems](overview/pottier.md)

* (17/09/2025) From operational semantics to interpreters (FP).
  * Introduction to this course ([slides](slides/fpottier-00.pdf))
  * Slides
    ([with    animations](slides/fpottier-01.pdf);
     [without animations](slides/fpottier-printing-01.pdf))
  * Optional extra material:
    Rocq in a nutshell;
    representing abstract syntax with binders
    ([with    animations](slides/fpottier-01b.pdf),
     [without animations](slides/fpottier-printing-01b.pdf))

* (24/09/2025) Syntactic proofs of type soundness
  for simply-typed lambda-calculus and for System F (FP).
  * [definition of simply-typed λ-calculus](coq/STLCDefinition.v)
  * [auxiliary lemmas and judgements](coq/STLCLemmas.v)
  * subject reduction and progress:
    [template](coq/STLCTypeSoundnessBlank.v),
    [solution](coq/STLCTypeSoundnessComplete.v)

* (01/10/2025) Algebraic data types and existential types (FP).
  * ([slides 03](slides/fpottier-03.pdf),
     [slides without animations 03](slides/fpottier-printing-03.pdf)).

* (08/10/2025) GADTs (FP).
  * ([slides 04](slides/fpottier-04.pdf),
     [slides without animations 04](slides/fpottier-printing-04.pdf)).

* (15/10/2025) Closure conversion and defunctionalization (FP).
  * ([slides 05](slides/fpottier-05.pdf),
     [slides without animations 05](slides/fpottier-printing-05.pdf)).

* (22/10/2025) Hindley-Milner type inference; bidirectional type inference (GS).

* (29/10/2025) *Break*

* (05/11/2025) System F with mutable state;
  the value restriction; type soundness (GS).
  * ([slides](slides/scherer-02.pdf))

### Semantic Proofs of Type Soundness and Logical Relations

* (12/11/2025)
  Unary logical relations for simple types;
  (weak) normalisation of simply-typed λ-calculus;
  unary logical relations for polymorphic types;
  (weak) normalisation of System F (GS).
  * ([slides](slides/scherer-01.pdf),
     [course notes from Lau Skorstengaard](https://arxiv.org/pdf/1907.11133.pdf)).

* (19/11/2025)
  Binary logical relations and parametricity;
  logical relations for mutable state, with step-indexing (GS).

* (26/11/2025) *Break*

* **(03/12/2025) mid-term exam**, in the usual room and at the usual time,
  **from 12:45 to 15:30**, without a break.
  The duration of the exam is 2h45.

### [Modular Programming and Modular Semantics](overview/zakowski.md)

* (10/12/2025) System Fω; modules (GS).
  * [State of the art of Module systems by C. Blaudeau (Ch.2)](https://clement.blaudeau.net/assets/pdf/thesis.pdf#page=23)
  * [Handout by D. Rémy](http://gallium.inria.fr/~remy/mpri/cours-fomega.pdf)

* (17/12/2025) Ad hoc polymorphism and overloading (DR).
  * ([summary](overview/remy.md))
  * ([handout](http://cambium.inria.fr/~remy/mpri/cours-overloading.pdf))

* (07/01/2026) Applicative functors and monads (YZ).

* (14/01/2026) The free monad, the delay monad, and interaction trees (YZ).

* (21/01/2026) Modular monadic semantics via layers of effect interpretations (YZ).

### [Programming with Resources in Rust](overview/jourdan.md)

* (28/01/2026) Introduction to programming in Rust (JHJ).

* (04/02/2026) Rust generics and traits (JHJ).

* (11/02/2026) Practicing Rust; concurrency (JHJ).

* (18/02/2026) Metatheory of Rust's type system;
  a semantic interpretation of types (JHJ).

* (25/02/2026) Translating Rust to purely functional code (JHJ).

* (04/03/2026) *break*

* (11/03/2026) **final exam**, in the usual room and at the usual time,
  **from 12:45 to 15:30**, without a break.
  The duration of the exam is 2h45.

## Evaluation of the course

Two written exams and one programming project are used to evaluate the
students.

The mid-term exam will take place on **03/12/2025**.

The deadline for the programming project is **28/02/2026**.

The final exam will take place on **11/03/2026**.

The coefficients are:

* **either** mid-term exam: 3 and final exam: 4
  **or** mid-term exam: 4 and final exam: 3
  (whichever is more advantageous for each student);
* programming project: 3.

Thus, the sum of the coefficients is 10.

The exams take place
in the usual room and at the usual time,
**from 12:45 to 15:30**, without a break.
The duration of the exam is 2h45.

Only **printed course notes** and **hand-written notes** are **allowed**
during the mid-term and final exams.
Electronic devices are **not allowed.**

Although the course evolves over time,
you are encouraged to have a look at the previous exams
and their solutions:

* final exam 2024-2025:
  [structural ML type inference](exams/final-2024-2025.pdf).
* mid-term exam 2024-2025:
  [a simple proof technique for certain parametricity results](exams/partiel-2024-2025.pdf).
* final exam 2023-2024:
  [circuits and functors](exams/final-2023-2024.pdf).
* mid-term exam 2023-2024:
  [fixed point combinators and recursive types](exams/partiel-2023-2024.pdf).
* final exam 2022-2023:
  [safe unchecked arrays; branded types in Rust](exams/final-2022-2023.pdf).
* mid-term exam 2022-2023:
  [extensible records](exams/partiel-2022-2023.pdf).
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

## Programming Project

Programming is an important part of the course. We give a mandatory
programming project, which counts for about a
third of the final grade.

The project for the year 2025-2026 will be made available in late fall or early winter.

The deadline was: **Friday, February 28, 2025**, at 23:59.

## Research Internship Proposals

We, the teachers of this course, usually post a few internship
offers at some point during the fall.

Please do not hesitate to talk to us (during the break or at the end of each
lecture), to contact us by email, or to visit us at our offices.

To find internships related to the topics of this course,
you may wish to also contact our colleagues:

* The [Cambium](https://cambium.inria.fr/) team at Inria Paris.
  Keywords:
  program verification in separation logic (Iris; Osiris),
  programming language design and implementation (OCaml),
  proof assistants (Coq; MetaCoq),
  type systems,
  verified compilation,
  and more.
* The [PPS](https://www.irif.fr/poles/pps/index) lab at IRIF,
  which includes the [Picube](https://www.irif.fr/equipes/picube/index) team.
  Keywords:
  programming language design and implementation (OCaml),
  proof assistants (Coq),
  semantics,
  type theory,
  and more.
* The [Prosecco](https://team.inria.fr/prosecco/) team at Inria Paris.
  Keywords:
  verification of security protocols (ProVerif; CryptoVerif; Squirrel),
  program verification,
  programming languages for the law (Catala),
  proof assistants (F*),
  software security,
  and more.
* The [Antique](https://team.inria.fr/antique/) team at ENS Paris.
  Keywords:
  abstract interpretation,
  program analysis,
  analysis of biological systems,
  and more.
* The [Parkas](https://parkas.di.ens.fr/) team at ENS Paris.
  Keywords:
  synchronous programming languages,
  type systems,
  verified compilation,
  and more.
* The [Partout](https://team.inria.fr/partout/) team at Inria Saclay.
  Keywords:
  connections between computation and deduction,
  proof theory,
  type theory,
  and more.
* The [Gallinette](https://gallinette.gitlabpages.inria.fr/website/)
  team at Inria Nantes.
  Keywords:
  formalized mathematics (Mathematical Components),
  proof assistants (Coq),
  type theory,
  and more.
* The [Toccata](https://toccata.gitlabpages.inria.fr/toccata/index.fr.html)
  team at Inria Saclay.
  Keywords:
  automated deduction,
  program verification,
  and more.
* The [Epicure](https://team.inria.fr/epicure/) team at Inria Rennes.
  Keywords:
  automated deduction,
  program analysis,
  semantics,
  software security,
  verified compilation,
  and more.
* The [Pesto](https://team.inria.fr/pesto/) team at Inria Nancy.
  Keywords:
  electronic voting,
  verification of security protocols,
  verified compilation,
  and more.
* The [Stamp](https://www.inria.fr/fr/stamp) team at Inria Sophia.
  Keywords:
  formalized mathematics (Mathematical Components),
  proof assistants (Coq),
  verification of security protocols (EasyCrypt),
  and more.
* The [Cash](https://www.ens-lyon.fr/LIP/CASH/?page_id=9) team at ENS Lyon.
  Keywords:
  compilation,
  formalized mathematics (Mathematical Components),
  program analysis,
  semantics,
  type systems,
  verified compilation,
  and more.
* The [Camus](https://team.inria.fr/camus/fr/) team at Inria Strasbourg.
  Keywords:
  compilation,
  parallelism,
  program verification,
  semantics,
  and more.

We also have contacts abroad, mainly in Europe, North America, and Asia.
If you would like to find an internship abroad,
do not hesitate to talk to us.

See also
[the official list of internship offers](https://mpri-master.ens.fr/doku.php?id=start#internships)
at MPRI.

## Recommended software

### Coq

Please install [opam](https://opam.ocaml.org/doc/Install.html) first.
A recent version is recommended.
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

### Rust

In order to participate to the hands-on exercises on Rust,
please install the following tools:

* The Rust compiler (version 1.41 or newer)
* The Cargo package manager (any compatible version)

Installation should be easy on any recent Linux distribution using
the system's package manager. An alternative is to follow
[these instructions](https://rustup.rs/).

In order to test the installation, the students are asked to use the Rust
compiler on the following program:

```rust
fn main() {
  let mut f = |x : i32| x;
  let _r : &mut dyn Fn(i32) -> i32 = &mut f;
  println!("{}", f(42))
}
```

If the compiler is correctly installed, then the command `rustc test.rs`
should produce an executable.

## Recommended Reading

[Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/),
Benjamin C. Pierce, MIT Press, 2002.

[Advanced Topics in Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/attapl/),
edited by Benjamin C. Pierce, MIT Press, 2005.

[Practical Foundations for Programming Languages, Second Edition](http://www.cs.cmu.edu/~rwh/pfpl.html),
Robert Harper, Cambridge University Press, 2016.
