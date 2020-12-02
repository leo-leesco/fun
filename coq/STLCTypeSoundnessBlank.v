Require Import MyTactics.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.
Require Import STLCDefinition.
Require Import STLCLemmas.

(*|

This is a failed attempt to prove the lemma `jt_te_substitution_0` in
a direct way, without introducing the auxiliary judgement `js`. See
STLCLemmas for a valid proof.

|*)

Goal (* jt_te_substitution_0 *)
  forall Delta t1 U,
  jt Delta t1 U ->
  forall Gamma t2 T,
  Delta = T .: Gamma ->
  jt Gamma t2 T ->
  jt Gamma t1.[t2/] U.
Proof.
  (* Let us attempt to naively prove this statement by induction. *)
Abort.

(*|

The subject reduction theorem, also known as type preservation:
the typing judgement is preserved by one step of reduction.

This is proved here for `cbv`, but could be proved for other notions
of reduction, such as `cbn`, or strong reduction.

|*)

Lemma jt_preservation:
  forall Gamma t T,
  jt Gamma t T ->
  forall t',
  cbv t t' ->
  jt Gamma t' T.
Proof.
Abort.

(*|

An inversion lemma: if a closed value admits a function type `TyFun T1 T2`,
then it must be a lambda-abstraction.

|*)

Lemma invert_jt_TyFun:
  forall Gamma t T1 T2,
  jt Gamma t (TyFun T1 T2) ->
  closed t ->
  is_value t ->
  exists t', t = Lam t'.
Proof.
Abort.

(*|

The progress theorem: a closed, well-typed term
must either be able to make one step of reduction
or be a value.

|*)

Lemma jt_progress:
  forall Gamma t T,
  jt Gamma t T ->
  closed t ->
  (exists t', cbv t t') \/ is_value t.
Ltac use_ih ih :=
  destruct ih; [ eauto with closed | unpack; eauto with red |  ].
Proof.
Abort.
