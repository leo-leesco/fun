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
