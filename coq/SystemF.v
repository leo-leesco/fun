Require Import MyTactics.
Require Import Sequences.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.

(* -------------------------------------------------------------------------- *)

(* The syntax of System F types. *)

Inductive ty :=
| TyVar (x : var)
| TyFun (A B : ty)
| TyAll (A : {bind ty}).

Instance Ids_ty : Ids ty. derive. Defined.
Instance Rename_ty : Rename ty. derive. Defined.
Instance Subst_ty : Subst ty. derive. Defined.
Instance SubstLemmas_ty : SubstLemmas ty. derive. Qed.

(* -------------------------------------------------------------------------- *)

(* A type environment is viewed as a total function of variables to types. *)

(* In principle, an environment should be modeled as a list of types, which
   represents a partial function of variables to types. This introduces a
   few complications, and is left as an exercise for the reader. *)

Definition tyenv := var -> ty.

(* -------------------------------------------------------------------------- *)

(* The typing judgement. *)

(* Our terms are pure lambda-terms, without any type annotations and without
   indication of the presence of type abstractions and type applications. We
   make this choice for several reasons. (1) It is nice to work directly with
   the syntax and operational semantics of the untyped lambda-calculus. This
   shows that the type system can be defined after the untyped calculus. (2)
   This means that terms do not contain any type variables. Thus, we never
   need to substitute a type for a type variable in a term. Terms contain just
   term variables, and types contain just type variables. This makes life
   easier. *)

(* The typing judgement is indexed with an integer [n] which counts the number
   of outstanding type abstractions and applications, that is, those that are
   not buried under a syntax-directed typing rule. This is used in the proof
   of the type substitution lemma [jtn_ty_substitution], where we prove that
   [n] is preserved, and in the proof of the inversion lemma [invert_JTNLam],
   which is by induction over [n]. *)

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

(* This hint means that [eauto with jtn] can apply the above typing rules. *)

Hint Constructors jtn : jtn.

(* -------------------------------------------------------------------------- *)

(* It is convenient to define a simpler typing judgement which is not indexed
   with an integer [n]. We use this judgement when we do not care about [n]. *)

Definition jt Gamma t T :=
  exists n,
  jtn n Gamma t T.

(* This hint means that [eauto with jt] can exploit the fact that
   [j n Gamma t T] implies [jt Gamma t T]. *)

Hint Unfold jt : jt.

(* It is convenient to reformulate the typing rules at the level of [jt].
   This is noisy/redundant, but nothing complicated is going on here. *)

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

(* This hint means that [eauto with jt] can use the above lemmas. *)

Hint Resolve JTVar JTLam JTApp JTTyAbs JTTyApp : jt.

(* Exercise: instead of defining [jt] in terms of [jtn], give a direct
   inductive definition of [jt]. Prove that [jt Gamma t T] is equivalent
   to [exists n, jtn n Gamma t T]. *)

(* -------------------------------------------------------------------------- *)

(* The typing judgement is preserved by a term renaming [xi], which maps term
   variables to term variables. Note that [xi] need not be injective. *)

Lemma jtn_te_renaming:
  forall n Gamma t U,
  jtn n Gamma t U ->
  forall Gamma' xi,
  Gamma = xi >>> Gamma' ->
  jtn n Gamma' t.[ren xi] U.
Proof.
  (* A detailed proof, where every case is dealt with explicitly: *)
  induction 1; intros; subst.
  (* JTNVar *)
  { asimpl. econstructor. eauto. }
  (* JTNLam *)
  { asimpl. econstructor. eapply IHjtn. autosubst. }
  (* JTNApp *)
  { asimpl. econstructor. eauto. eauto. }
  (* JTNTyAbs *)
  { asimpl. econstructor. eapply IHjtn. autosubst. autosubst. }
  (* JTNTyApp *)
  { asimpl. econstructor. eauto. eauto. }
Restart.
  (* A shorter script, where all cases are dealt with in the same way: *)
  induction 1; intros; subst; asimpl; econstructor; eauto with autosubst.
Qed.

(* As a corollary, the same is true of the judgement [jt]. *)

Lemma jt_te_renaming:
  forall Gamma t U,
  jt Gamma t U ->
  forall Gamma' xi,
  Gamma = xi >>> Gamma' ->
  jt Gamma' t.[ren xi] U.
Proof.
  unfold jt. intros. unpack. eauto using jtn_te_renaming.
Qed.

(* As a corollary, [jt] is preserved by the renaming [(+1)]. *)

Lemma jt_te_renaming_0:
  forall Gamma t T U,
  jt Gamma t U ->
  jt (T .: Gamma) (lift 1 t) U.
Proof.
  intros. eapply jt_te_renaming. eauto. autosubst.
Qed.

(* -------------------------------------------------------------------------- *)

(* The typing judgement is preserved by a type substitution [theta], which
   maps type variables to types. *)

(* We prove that the measure [n] is preserved by such a substitution. This
   is required in the proof of [invert_JTNLam], where we apply a substitution
   to the type derivation before exploiting the induction hypothesis. *)

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
  { econstructor. eapply IHjtn. eauto with autosubst. eauto. }
  (* JTNApp *)
  { econstructor. eapply IHjtn1. eauto. asimpl. eauto. eauto. }
  (* JTNTyAbs *)
  { econstructor. eapply IHjtn. eauto. eauto. autosubst. }
  (* JTNTyApp *)
  { econstructor. eapply IHjtn. eauto. autosubst. autosubst. }
Restart.
  (* A shorter script, where all cases are dealt with in the same way: *)
  induction 1; intros; subst; econstructor; eauto with autosubst.
Qed.

(* As a corollary, the same is true of the judgement [jt]. *)

Lemma jt_ty_substitution:
  forall Gamma t T theta,
  jt Gamma t T ->
  jt (Gamma >> theta) t T.[theta].
Proof.
  unfold jt. intros. unpack. eauto using jtn_ty_substitution.
Qed.

(* As another corollary, [jtn] is preserved by a substitution of the type [U]
   for the type variable 0. If this variable does not occur in [Gamma], then
   [Gamma] is unaffected, except for the necessary renumbering. *)

Lemma jtn_ty_substitution_0:
  forall n Gamma t T U,
  jtn n (Gamma >> ren (+1)) t T ->
  jtn n Gamma t T.[U/].
Proof.
  intros. eapply jtn_ty_substitution; eauto. autosubst.
Qed.

(* -------------------------------------------------------------------------- *)

(* The typing judgement is extended to substitutions. [sigma] has type [Delta]
   if and only if, for every variable [x], [sigma x] has type [Delta x]. This
   is relative to a type environment [Gamma]. *)

Definition js Gamma sigma Delta :=
  forall x : var,
  jt Gamma (sigma x) (Delta x).

(* Basic lemmas about [js]. *)

Lemma js_ids:
  forall Gamma,
  js Gamma ids Gamma.
Proof.
  unfold js. eauto with jt.
Qed.

Lemma js_cons:
  forall Gamma t sigma T Delta,
  jt Gamma t T ->
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
  { eauto with jt. }
  { eauto using jt_te_renaming_0. }
Qed.

Lemma js_ty_substitution:
  forall Gamma sigma Delta theta,
  js Gamma sigma Delta ->
  js (Gamma >> theta) sigma (Delta >> theta).
Proof.
  unfold js. eauto using jt_ty_substitution.
Qed.

(* -------------------------------------------------------------------------- *)

(* The typing judgement is preserved by a well-typed substitution [sigma]
   of a term for a term variable. This property is exploited in the proof
   of subject reduction, in the case of beta-reduction. *)

Lemma jtn_te_substitution:
  forall n Delta t U,
  jtn n Delta t U ->
  forall Gamma sigma,
  js Gamma sigma Delta ->
  jt Gamma t.[sigma] U.
Proof.
  (* A short script, where all cases are dealt with in the same way: *)
  induction 1; intros; subst; asimpl;
  eauto using js_up, js_ty_substitution with jt.
Qed.

(* As a corollary, an analogous statement is true of the judgement [jt]. *)

Lemma jt_te_substitution:
  forall Delta t U,
  jt Delta t U ->
  forall Gamma sigma,
  js Gamma sigma Delta ->
  jt Gamma t.[sigma] U.
Proof.
  unfold jt at 1. intros. unpack. eauto using jtn_te_substitution.
Qed.

(* As a corollary, the typing judgement is preserved by a substitution
   of a term of type [T] for a variable of type [T]. *)

Lemma jt_te_substitution_0:
  forall Gamma t1 t2 T U,
  jt (T .: Gamma) t1 U ->
  jt Gamma t2 T ->
  jt Gamma t1.[t2/] U.
Proof.
  eauto using jt_te_substitution, js_ids, js_cons.
Qed.

(* -------------------------------------------------------------------------- *)

(* As a tool in the statement of the inversion lemma [invert_JTNLam], let us
   define a subtyping relation between types. This relation is defined by
   just one rule: the type [TyAll T] is a subtype of the type [T.[U/]]. *)

Inductive sub : ty -> ty -> Prop :=
| Sub:
    forall T T' U,
    T' = T.[U/] ->
    sub (TyAll T) T'.

(* -------------------------------------------------------------------------- *)

(* This is an inversion lemma for the typing rule [JTNLam]. A simplified version
   of the statement is as follows: if under [Gamma] a lambda-abstraction [Lam t]
   has type [TyFun T U], then it must be the case that, under the extended
   environment [T .: Gamma], the term [t] has type [U]. *)

(* This simplified statement cannot be proved by induction. Instead, we propose
   a more general statement, where [Lam t] has type [T'] and [T'] is a subtype
   of [TyFun T U]. We use the relation [star sub], instead of just [sub], so as
   to allow for a sequence of subtyping steps. *)

(* The proof is by induction over [n], and this is the basic reason why the
   judgement [jtn] must be parameterized with [n]. The computational content
   of this proof is to reduce all type redexes found at the root of the type
   derivation. (A type redex is an application of a type abstraction to a type,
   that is, a situation where [JTNApp] is used just after [JTNAbs].) We must
   prove that this process terminates, and the fact that [n] decreases is the
   basic reason why it terminates. *)

Lemma invert_JTNLam:
  forall n Gamma t T' T U,
  jtn n Gamma (Lam t) T' ->
  star sub T' (TyFun T U) ->
  jt (T .: Gamma) t U.
Proof.
  (* By induction on [n], and by case analysis on the typing judgement. *)
  induction n; inversion 1; intros; subst.

  (* Case: [n] is 0. Then, the type derivation must end with [JTNLam]. *)
  { (* We have a hypothesis [star sub (TyFun T' U') (TyFun T U)]. Considering
       the definition of the relation [sub], this must be a sequence of zero
       subtyping steps, so we must have [T' = T] and [U' = U]. To let Coq see
       this, it suffices to perform case analysis. *)
    pick star invert; [ | pick sub invert ].
    (* The result is then immediate. *)
    eauto with jt. }

  (* Case: [n] is [S m], and the type derivation ends with [JTNAbs]. *)
  { (* We have a hypothesis [star sub (TyAll T') (TyFun T U)]. Considering
       the definition of the relation [sub], this must be a sequence of at
       least one subtyping step. To let Coq see this, we again perform case
       analysis. *)
    pick star invert. pick sub invert.
    (* Thus, we have one subtyping step from [TyAll T'] to [T'.[U'/]], and
       from there, the rest of the subtyping sequence, to [TyFun T U]. We
       are looking at a type abstraction: the idea is to instantiate this
       abstraction by substituting the type [U'] for the type variable [0],
       and then to use the induction hypothesis. (This exploits the fact
       that [jtn_ty_substitution] preserves the size of the type derivation.)
       Or, to put it the other way around, let us instruct Coq that the proof
       is finished by applying the induction hypothesis, and let us see what
       the goal then becomes: *)
    eapply IHn; [ | eauto ].
    (* The goal is now to prove that [Lam t] has type [T'.[U'/]] under [Gamma].
       We know that it has [TyAll T'] under [Gamma >> ren (+1)], so this is
       exactly the type substitution lemma. *)
    eauto using jtn_ty_substitution_0. }

  (* Case: [n] is [S m], and the type derivation ends with [JTNApp]. *)
  { (* In that case, it suffices to invoke the induction hypothesis. The
       subtyping sequence [star sub ...] grows by one, as one more step is
       prepended to it. This is precisely the reason why the lemma was
       formulated in this general form. *)
    eapply IHn; eauto using sub with sequences. }

Qed.

(* -------------------------------------------------------------------------- *)

(* The typing judgement is preserved by one step of reduction. *)

(* This is proved here for [cbv], but could be proved for other notions
   of reduction, such as [cbn], or strong reduction. *)

Lemma jtn_preservation:
  forall n Gamma t T,
  jtn n Gamma t T ->
  forall t',
  cbv t t' ->
  jt Gamma t' T.
Proof.
  (* By induction on the type derivation. *)
  induction 1; intros; subst; try solve [ invert_cbv ].
  (* JTNApp *)
  { (* By case analysis on [cbv t t']. *)
    invert_cbv.
    (* RedBetaV. A beta-redex, [App (Lam t) v], reduces to [t.[v/]]. *)
    { (* The idea is to substitute the value [v] for the variable [0]. *)
      eapply jt_te_substitution_0; eauto with jt.
      (* This requires us to prove that the function body [t] is well-typed
         under an extended type environment [T .: Gamma]. Fortunately, this
         is guaranteed by the inversion lemma [invert_JTNLam]. *)
      eapply invert_JTNLam; eauto with sequences. }
    (* RedAppL. *)
    { eauto with jt. }
    (* RedAppVR. *)
    { eauto with jt. }
  }
  (* JTNTyAbs *)
  { eauto with jt. }
  (* JTNTyApp *)
  { eauto with jt. }
Qed.

Lemma jt_preservation:
  forall Gamma t T t',
  jt Gamma t T ->
  cbv t t' ->
  jt Gamma t' T.
Proof.
  unfold jt at 1. intros. unpack. eauto using jtn_preservation.
Qed.
