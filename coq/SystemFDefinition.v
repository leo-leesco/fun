Require Import MyTactics.
Require Import Sequences.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.

(*|

------------------------
Syntax of System F types
------------------------

Here is the syntax of System F types:

|*)

Inductive ty :=
| TyVar (x : var)
| TyFun (A B : ty)
| TyAll (A : {bind ty}).

Instance Ids_ty : Ids ty. derive. Defined.
Instance Rename_ty : Rename ty. derive. Defined.
Instance Subst_ty : Subst ty. derive. Defined.
Instance SubstLemmas_ty : SubstLemmas ty. derive. Qed.

(*|

A type environment is a total function of variables to types.

|*)

Definition tyenv := var -> ty.

(*|

--------------------
The typing judgement
--------------------

|*)
(*|

Our terms are pure lambda-terms, without any type annotations and without
indication of the presence of type abstractions and type applications. We make
this choice for several reasons:

* It is nice to work directly with the syntax and operational semantics of the
  untyped lambda-calculus. This shows that the type system can be defined
  after the untyped calculus.

* This means that terms do not contain any type variables. Thus, we never need
  to substitute a type for a type variable in a term. Terms contain just term
  variables, and types contain just type variables. This makes life easier.

|*)

Inductive jf : tyenv -> term -> ty -> Prop :=
| JFVar:
    forall Gamma x T,
    Gamma x = T ->
    jf Gamma (Var x) T
| JFLam:
    forall Gamma t T U,
    jf (T .: Gamma) t U ->
    jf Gamma (Lam t) (TyFun T U)
| JFApp:
    forall Gamma t1 t2 T U,
    jf Gamma t1 (TyFun T U) ->
    jf Gamma t2 T ->
    jf Gamma (App t1 t2) U
| JFTyAbs:
    forall Gamma Gamma' t T,
    jf Gamma' t T ->
    Gamma' = Gamma >> ren (+1) ->
    jf Gamma t (TyAll T)
| JFTyApp:
    forall Gamma t T U T',
    jf Gamma t (TyAll T) ->
    T' = T.[U/] ->
    jf Gamma t T'
.

(*|

The following hint allows `eauto with jf` to apply the above typing rules.

|*)

Hint Constructors jf : jf.
