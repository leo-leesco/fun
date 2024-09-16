Require Import MyTactics.
Require Import Sequences.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.
Require Import SystemFDefinition.

(*|

-----------------------------------------
A size-indexed typing judgement for terms
-----------------------------------------

|*)
(*|

This typing judgement is indexed with an integer `n` which counts the
number of *outstanding* type abstractions and type applications, that
is, the number of type abstractions and type applications that are not
buried under a syntax-directed typing rule.

This integer index is used in the proof of the type substitution lemma
`jtn_ty_substitution`, where we prove that `n` is preserved, and in
the proof of the inversion lemma `invert_jtn_Lam_TyFun`, which is
carried out by induction over `n`.

|*)

Inductive jtn : nat -> tyenv -> term -> ty -> Prop :=
| JTNVar:
    forall Gamma x T,
    Gamma x = T ->
    jtn 0 Gamma (Var x) T
| JTNLam:
    forall n Gamma t T U,
    jtn n (T .: Gamma) t U ->
    jtn 0 Gamma (Lam t) (TyFun T U)
| JTNApp:
    forall n1 n2 Gamma t1 t2 T U,
    jtn n1 Gamma t1 (TyFun T U) ->
    jtn n2 Gamma t2 T ->
    jtn 0 Gamma (App t1 t2) U
| JTNTyAbs:
    forall n Gamma Gamma' t T,
    jtn n Gamma' t T ->
    Gamma' = Gamma >> ren (+1) ->
    jtn (S n) Gamma t (TyAll T)
| JTNTyApp:
    forall n Gamma t T U T',
    jtn n Gamma t (TyAll T) ->
    T' = T.[U/] ->
    jtn (S n) Gamma t T'
.

(*|

The following hint allows `eauto with jtn` to apply the above typing rules.

|*)

Global Hint Constructors jtn : jtn.

(*|
-----------------------------------------
Equivalence between the typing judgements
-----------------------------------------
|*)

(*|

It is convenient to define a simpler typing judgement which is not indexed
with an integer `n`. We use this judgement when we do not care about `n`.

|*)

Definition jt Gamma t T :=
  exists n,
  jtn n Gamma t T.

(*|

The following hint allows `eauto with jt` to exploit the fact that
`j n Gamma t T` implies `jt Gamma t T`.

|*)

Global Hint Unfold jt : jt.

(*|

It is convenient to reformulate the typing rules at the level of `jt`.
This is somewhat redundant, but nothing complicated is going on here.

|*)

Lemma JTVar:
  forall Gamma x T,
  Gamma x = T ->
  jt Gamma (Var x) T.
Proof.
  unfold jt. intros. unpack. eauto using jtn.
Qed.

Lemma JTLam:
  forall Gamma t T U,
  jt (T .: Gamma) t U ->
  jt Gamma (Lam t) (TyFun T U).
Proof.
  unfold jt. intros. unpack. eauto using jtn.
Qed.

Lemma JTApp:
  forall Gamma t1 t2 T U,
  jt Gamma t1 (TyFun T U) ->
  jt Gamma t2 T ->
  jt Gamma (App t1 t2) U.
Proof.
  unfold jt. intros. unpack. eauto using jtn.
Qed.

Lemma JTTyAbs:
  forall Gamma Gamma' t T,
  jt Gamma' t T ->
  Gamma' = Gamma >> ren (+1) ->
  jt Gamma t (TyAll T).
Proof.
  unfold jt. intros. unpack. eauto using jtn.
Qed.

Lemma JTTyApp:
  forall Gamma t T U T',
  jt Gamma t (TyAll T) ->
  T' = T.[U/] ->
  jt Gamma t T'.
Proof.
  unfold jt. intros. unpack. eauto using jtn.
Qed.

(*|

The following hint allows `eauto with jt` to use the above lemmas.

|*)

Global Hint Resolve JTVar JTLam JTApp JTTyAbs JTTyApp : jt.

(*|

The judgements `jt` and `jf` are equivalent. So, we have just given an
alternate definition of System F.

|*)

Lemma jtn_jf:
  forall n Gamma t T,
  jtn n Gamma t T ->
  jf Gamma t T.
Proof.
  induction 1; intros; subst; eauto with jf.
Qed.

Lemma jt_jf:
  forall Gamma t T,
  jt Gamma t T ->
  jf Gamma t T.
Proof.
  unfold jt. intros. unpack. eauto using jtn_jf.
Qed.

Lemma jf_jt:
  forall Gamma t T,
  jf Gamma t T ->
  jt Gamma t T.
Proof.
  induction 1; intros; subst; eauto with jt.
Qed.

(*|
-----------------------------------------
Substitutions of types for type variables
-----------------------------------------
|*)

(*|

The typing judgement `jtn` is preserved by a type substitution `theta`,
which maps type variables to types.

We prove that the measure `n` is preserved by such a substitution.
This is required in the proof of `invert_jtn_Lam_TyFun`, where we
apply a substitution to the type derivation before exploiting the
induction hypothesis.

|*)

Lemma jtn_ty_substitution:
  forall n Gamma t T,
  jtn n Gamma t T ->
  forall Gamma' T' theta,
  Gamma' = Gamma >> theta ->
  T' = T.[theta] ->
  jtn n Gamma' t T'.
Proof.
  (* A detailed proof, where every case is dealt with explicitly: *)
  induction 1; intros; subst.
  (* JTNVar *)
  { econstructor. autosubst. }
  (* JTNLam *)
  { econstructor. eapply IHjtn.
      eauto with autosubst.
      eauto. }
  (* JTNApp *)
  { econstructor.
      eapply IHjtn1.
        eauto.
        asimpl. eauto.
      eauto. }
  (* JTNTyAbs *)
  { econstructor.
      eapply IHjtn.
        eauto.
        eauto.
      autosubst. }
  (* JTNTyApp *)
  { econstructor.
      eapply IHjtn.
        eauto.
        autosubst.
      autosubst. }
Restart.
  (* A shorter script, where all cases are dealt with uniformly: *)
  induction 1; intros; subst;
  econstructor; eauto with autosubst.
Qed.

(*|

As a corollary, if the term `t` has type `T`
under a type environment that extends `Gamma` with one type variable,
then for every type `U`,
the term `t` has type `T.[U/]` under `Gamma`.

Again, the measure `n` is preserved by this substitution.

|*)

Lemma jtn_ty_substitution_0:
  forall n Gamma t T U,
  jtn n (Gamma >> ren (+1)) t T ->
  jtn n Gamma t T.[U/].
Proof.
  intros.
  eapply jtn_ty_substitution; eauto.
  autosubst.
Qed.

(*|

As a corollary, the same properties hold of the judgement `jf`.

|*)

Lemma jf_ty_substitution:
  forall Gamma t T theta,
  jf Gamma t T ->
  jf (Gamma >> theta) t T.[theta].
Proof.
  intros.
  forward jf_jt.
  unfold jt in *. unpack.
  forward jtn_ty_substitution.
  eauto using jtn_jf.
Qed.

Lemma jf_ty_substitution_0:
  forall Gamma t T U,
  jf (Gamma >> ren (+1)) t T ->
  jf Gamma t T.[U/].
Proof.
  intros.
  forward jf_jt.
  unfold jt in *. unpack.
  forward jtn_ty_substitution_0.
  eauto using jtn_jf.
Qed.

(*|
---------------------------
Renamings of term variables
---------------------------
|*)

(*|

The typing judgement is preserved by a renaming `xi` that maps
term variables to term variables. Note that `xi` need not be
injective.

|*)

Lemma jf_te_renaming:
  forall Gamma t U,
  jf Gamma t U ->
  forall Gamma' xi,
  Gamma = xi >>> Gamma' ->
  jf Gamma' t.[ren xi] U.
Proof.
  (* A detailed proof, where every case is dealt with explicitly: *)
  induction 1; intros; subst.
  (* JFVar *)
  { asimpl. econstructor.
      eauto. }
  (* JFLam *)
  { asimpl. econstructor.
      eapply IHjf. autosubst. }
  (* JFApp *)
  { asimpl. econstructor.
      eauto.
      eauto. }
  (* JFTyAbs *)
  { asimpl. econstructor.
      eapply IHjf. autosubst.
      autosubst. }
  (* JFTyApp *)
  { asimpl. econstructor.
      eauto.
      eauto. }
Restart.
  (* A shorter script, where all cases are dealt with uniformly: *)
  induction 1; intros; subst;
  asimpl; econstructor; eauto with autosubst.
Qed.

(*|

As a corollary, `jf` is preserved by the renaming `(+1)`.

|*)

Lemma jf_te_renaming_0:
  forall Gamma t T U,
  jf Gamma t U ->
  jf (T .: Gamma) (lift 1 t) U.
Proof.
  intros. eapply jf_te_renaming. eauto. autosubst.
Qed.

(*|
-----------------------------------------
Substitutions of terms for term variables
-----------------------------------------
|*)

(*|

The typing judgement is extended to substitutions.

|*)

Definition js Gamma sigma Delta :=
  forall x : var,
  jf Gamma (sigma x) (Delta x).

(*|

The following are basic lemmas about `js`.

|*)

Lemma js_ids:
  forall Gamma,
  js Gamma ids Gamma.
Proof.
  unfold js. eauto with jf.
Qed.

Lemma js_cons:
  forall Gamma t sigma T Delta,
  jf Gamma t T ->
  js Gamma sigma Delta ->
  js Gamma (t .: sigma) (T .: Delta).
Proof.
  intros. intros [|x]; asimpl; eauto.
Qed.

Lemma js_up:
  forall Gamma sigma Delta T,
  js Gamma sigma Delta ->
  js (T .: Gamma) (up sigma) (T .: Delta).
Proof.
  intros. intros [|x]; asimpl.
  { eauto with jf. }
  { eauto using jf_te_renaming_0. }
Qed.

(*|

In the following statement, `theta` is a substitution of types for
type variables. It is post-composed with the type environments
`Gamma` and `Delta`.

|*)

Lemma js_ty_substitution:
  forall Gamma sigma Delta theta,
  js Gamma sigma Delta ->
  js (Gamma >> theta) sigma (Delta >> theta).
Proof.
  unfold js. eauto using jf_ty_substitution.
Qed.

(*|

The typing judgement is preserved by a well-typed substitution `sigma`
of (all) term variables to terms.

|*)

Lemma jf_te_substitution:
  forall Delta t U,
  jf Delta t U ->
  forall Gamma sigma,
  js Gamma sigma Delta ->
  jf Gamma t.[sigma] U.
Proof.
  induction 1; intros; subst; asimpl;
  eauto using js_up, js_ty_substitution with jf.
Qed.

(*|

As a corollary, the typing judgement is preserved by a well-typed
substitution of one term for one variable, namely variable 0.

This property is exploited in the proof of subject reduction, in the
case of beta-reduction.

|*)

Lemma jf_te_substitution_0:
  forall Gamma t1 t2 T U,
  jf (T .: Gamma) t1 U ->
  jf Gamma t2 T ->
  jf Gamma t1.[t2/] U.
Proof.
  eauto using jf_te_substitution, js_ids, js_cons.
Qed.
