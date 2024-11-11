Require Import MyTactics.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.

(*|

-----
Types
-----

Here is the syntax of simple types:

|*)

Inductive ty :=
| TyVar (x : var)
| TyFun (A B : ty).

(*|

A type environment is viewed as a total function of variables to types.

In principle, an environment should be modeled as a list of types, which
represents a partial function of variables to types. This introduces a few
complications, and is left as an exercise for the reader.

|*)

Definition tyenv := var -> ty.

(*|

--------------------
The typing judgement
--------------------

The simply-typed lambda-calculus is defined by the following three
typing rules. (For simplicity, the typing rule for `Let` is omitted.)

|*)

Inductive jt : tyenv -> term -> ty -> Prop :=
| JTVar:
    forall Gamma x T,
    Gamma x = T ->
    jt Gamma (Var x) T
| JTLam:
    forall Gamma t T U,
    jt (T .: Gamma) t U ->
    jt Gamma (Lam t) (TyFun T U)
| JTApp:
    forall Gamma t1 t2 T U,
    jt Gamma t1 (TyFun T U) ->
    jt Gamma t2 T ->
    jt Gamma (App t1 t2) U
.

(*|

The tactic `pick_jt t` picks a hypothesis `h` whose statement is a typing
judgement about the term `t`, and passes `h` to the Ltac continuation `k`.

Thus, for instance, `pick_jt t invert` selects a typing judgement that is
at hand for the term `t` and inverts it.

|*)

Ltac pick_jt t k :=
  match goal with h: jt _ t _ |- _ => k h end.

(*|

The following hint allows `eauto with jt` to apply the above typing rules.

|*)

Global Hint Constructors jt : jt.
