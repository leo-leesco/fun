# Functional programming and type systems (2023-2024)

This page supplements
[the official page of MPRI 2-4](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-4-2).

This course presents the principles, formalisms, and mathematical techniques
that underlie many of today's typed programming languages, including OCaml,
Haskell, and Rust.
Here are some [introductory slides](slides/fpottier-00.pdf).

The course is taught by
[Pierre-Evariste Dagand](https://www.irif.fr/~dagand/) (PED),
[Jacques-Henri Jourdan](https://jhjourdan.mketjh.fr/) (JHJ),
[François Pottier](http://cambium.inria.fr/~fpottier/) (FP)
(*head*),
and
[Gabriel Scherer](http://www.lix.polytechnique.fr/Labo/Gabriel.Scherer/) (GS).

The content of the course is partly renewed in 2023-2024. In particular, we
will teach both **syntactic and semantic proofs of type soundness**, place
more emphasis on **logical relations**, including **logical relations in
Iris**, and present **two distinct algorithmic approaches to type inference**.

## Location and Schedule

The lectures take place at University of Paris,
Bâtiment Sophie Germain,
in room **1002**.

They are scheduled on **Wednesdays** from **12:45** to **15:30**.
There is a 15-minute break in the middle of each lecture,
so each lecture lasts 2h30.

## Syllabus and Time Table

The syllabus is organized in four main segments of five lectures each.

### [Operational Semantics, Type Systems, and Program Transformations](overview/pottier.md)

* (13/09/2023) Syntax, semantics, and interpreters (FP).
  * Introduction to this course
      ([slides 00](slides/fpottier-00.pdf)).
  * From operational semantics to interpreters
      ([slides 01](slides/fpottier-01.pdf),
       [slides without animations 01](slides/fpottier-printing-01.pdf)).
  * *Optional additional material*: towards machine-checked proofs
      ([slides 01b](slides/fpottier-01b.pdf),
       [slides without animations 01b](slides/fpottier-printing-01b.pdf))
      ([λ-calculus in Coq](coq/DemoSyntaxReduction.v))
      ([λ-calculus in OCaml](ocaml/pottier/Lambda.ml)).
* (20/09/2023) System F and a syntactic proof of its type soundness (FP).
  * ([slides 02](slides/fpottier-02.pdf),
     [slides without animations 02](slides/fpottier-printing-02.pdf)).
* (27/09/2023) Algebraic data types, existential types, and GADTs (FP).
  * ([slides 03](slides/fpottier-03.pdf),
     [slides without animations 03](slides/fpottier-printing-03.pdf)).
* (04/10/2023) GADTs, continued (FP).
  * (see slides of previous week).
* (11/10/2023) Closure conversion and defunctionalization (FP).
  * ([slides 04](slides/fpottier-04.pdf),
     [slides without animations 04](slides/fpottier-printing-04.pdf)).
* (read at home) (optional) The CPS transformation (FP).
  * ([slides 05](slides/fpottier-05.pdf),
     [slides without animations 05](slides/fpottier-printing-05.pdf)).

### Semantic Proofs of Type Soundness and Logical Relations

* (18/10/2023) Semantic interpretation of types: unary logical relations (GS).
  + ([slides](slides/scherer-01.pdf),
     [course notes from Lau Skorstengaard](https://arxiv.org/pdf/1907.11133.pdf))
* (25/10/2023) Binary logical relations and parametricity (GS).
  + (same slides)
* (01/11/2023) *holiday*
* (08/11/2023) Mutable state and the value restriction (GS).
  + ([slides](slides/scherer-02.pdf))
* (15/11/2023) Strong normalization for System F in Coq (GS).
  + ([in CBV](https://github.com/coq-community/autosubst/blob/master/examples/ssr/SystemF_CBV.v),
     [full reduction](https://github.com/coq-community/autosubst/blob/master/examples/ssr/SystemF_SN.v))
* (22/11/2023) Semantic type soundness for System F
               with mutable state in Coq/Iris (JHJ).
* **(29/11/2023) mid-term exam**, in the usual room and at the usual time,
  **from 12:45 to 15:30**, without a break.
  The duration of the exam is 2h45.

### Typed Programming

* (06/12/2023) Ad-hoc polymorphism and overloading (PED).
* (13/12/2023) Applicative functors and monads (PED).
* (20/12/2023) Hindley-Milner type inference and elaboration (GS).
* (10/01/2024) Bidirectional type inference and elaboration (PED).
* (17/01/2024) System Fω and modules (PED).

### Programming with Resources in Rust

* (24/01/2024) Introduction to Rust programming (JHJ).
* (31/01/2024) When the aliasing discipline is too strong (JHJ).
* (07/02/2024) Multi-threading (JHJ).
* (14/02/2024) Metatheory of Rust's type system (JHJ).
* (21/02/2024) Exercise session (PED).
* (28/02/2024) *break*
* (06/03/2024) **final exam**

## Evaluation of the course

Two written exams and one programming project are used to evaluate the
students.

The mid-term and final exams will take place on
**29/11/2023** and **06/03/2024**.

The exam takes place
in the usual room and at the usual time,
**from 12:45 to 15:30**, without a break.
The duration of the exam is 2h45.

Only **printed course notes** and **hand-written notes** are **allowed**
during the mid-term and final exams.
Electronic devices are **not allowed.**

Although the course evolves over time,
you are encouraged to have a look at the previous exams
and their solutions:

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

<!-- TODO
**The project is now available!**
It inhabits a [separate repository](https://github.com/fpottier/mpri-2.4-projet-2022-2023).
This may be helpful in case we need to make changes
(clarifications or additions) to it.
We suggest that you fork this repository
and work on your fork.

The deadline for submitting your project is **February 14, 2024**.
-->

Please do not hesitate to ask questions about the project,
of an administrative or technical nature,
to [François Pottier](francois.pottier@inria.fr).

## Research Internship Proposals

We are planning to post a few internship proposals
at some point during the fall or winter.

The internship offers posted by
[the Prosecco team](https://team.inria.fr/prosecco/job-offers/)
at Inria Paris are also relevant.

Please do not hesitate to talk to us (during the break or at the end of each
lecture), to contact us by email, or to visit us at our offices.

See also
[the official list of internship offers](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=internships)
at MPRI.

## Recommended software

### Coq

Please install [opam](https://opam.ocaml.org/doc/Install.html) first.
A recent version is recommended (at the time of writing, 2.1.5).
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
