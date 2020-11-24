Require Import Sequences.
Require Import Relations.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusReduction.
Require Import LambdaCalculusParallelReduction.
Require Import MyTactics.

(* This is an adaptation of the paper "A Simple Proof of Call-by-Value
   Standardization", by Karl Crary (2009). We establish two main results:

   First, parallel call-by-value reduction is adequate, i.e., is contained in
   contextual equivalence: if [t1] parallel-reduces to [t2], then [t1] halts
   if and only if [t2] halts (where halting is considered with respect to
   ordinary call-by-value reduction, [cbv]).

   Second, every call-by-value reduction sequence can be put in a standard
   form, as defined by the predicate [stdred]. *)

(* -------------------------------------------------------------------------- *)

(* "Evaluation" in Crary's paper is [cbv] here. Parallel reduction in Crary's
   paper is [pcbv] here. Internal parallel reduction, [ipcbv], is defined as
   follows. It is a restricted version of parallel reduction: it is allowed to
   act only under lambda, in the right-hand side of an application whose
   left-hand side is not a value, and in the right-hand side of [Let]. *)

Inductive ipcbv : term -> term -> Prop :=
| IRedVar:
    forall x,
    ipcbv (Var x) (Var x)
| IRedLam:
    forall t1 t2,
    pcbv t1 t2 ->
    ipcbv (Lam t1) (Lam t2)
| IRedAppLRNonValue:
    forall t1 t2 u1 u2,
    ~ is_value t1 ->
    ipcbv t1 t2 ->
    pcbv u1 u2 ->
    ipcbv (App t1 u1) (App t2 u2)
| IRedAppLR:
    forall t1 t2 u1 u2,
    is_value t1 -> (* wlog; see [ipcbv_IRedAppLR] below *)
    ipcbv t1 t2 ->
    ipcbv u1 u2 ->
    ipcbv (App t1 u1) (App t2 u2)
| IRedLetLR:
    forall t1 t2 u1 u2,
    ipcbv t1 t2 ->
    pcbv u1 u2 ->
    ipcbv (Let t1 u1) (Let t2 u2)
.

Local Hint Constructors ipcbv : red obvious.

(* [ipcbv] is a subset of [pcbv]. *)

Lemma ipcbv_subset_pcbv:
  forall t1 t2,
  ipcbv t1 t2 ->
  pcbv t1 t2.
Proof.
  induction 1; obvious.
Qed.

Local Hint Resolve ipcbv_subset_pcbv : red obvious.

(* The side condition [is_value t1] in [IRedAppLR] does not cause any loss
   of expressiveness, as the previous rule covers the case where [t1] is
   not a value. *)

Lemma ipcbv_IRedAppLR:
  forall t1 t2 u1 u2,
  ipcbv t1 t2 ->
  ipcbv u1 u2 ->
  ipcbv (App t1 u1) (App t2 u2).
Proof.
  intros. value_or_nonvalue t1; obvious.
Qed.

Local Hint Resolve ipcbv_IRedAppLR : red obvious.

(* [ipcbv] is reflexive. *)

Lemma ipcbv_refl:
  forall t,
  ipcbv t t.
Proof.
  induction t; eauto using red_refl with obvious.
Qed.

Local Hint Resolve ipcbv_refl : core.

(* [ipcbv] preserves values, both ways. *)

Lemma ipcbv_preserves_values:
  forall v1 v2, ipcbv v1 v2 -> is_value v1 -> is_value v2.
Proof.
  induction 1; is_value.
Qed.

Lemma ipcbv_preserves_values_reversed:
  forall v1 v2, ipcbv v1 v2 -> is_value v2 -> is_value v1.
Proof.
  induction 1; is_value.
Qed.

Lemma ipcbv_preserves_values_reversed_contrapositive:
  forall v1 v2, ipcbv v1 v2 -> ~ is_value v1 -> ~ is_value v2.
Proof.
  induction 1; is_value.
Qed.

Local Hint Resolve
  ipcbv_preserves_values ipcbv_preserves_values_reversed
  ipcbv_preserves_values_reversed_contrapositive : core.

Lemma star_ipcbv_preserves_values_reversed:
  forall v1 v2, star ipcbv v1 v2 -> is_value v2 -> is_value v1.
Proof.
  induction 1; eauto.
Qed.

Local Hint Resolve star_ipcbv_preserves_values_reversed : core.

(* Reverse internal parallel reduction preserves the property of being stuck
   and (therefore) the property of being irreducible. *)

Lemma reverse_ipcbv_preserves_stuck:
  forall t1 t2,
  ipcbv t1 t2 ->
  stuck t2 ->
  stuck t1.
Proof.
  induction 1; inversion 1; subst; eauto with stuck.
  { false. obvious. }
  { false. obvious. }
  { eapply StuckApp; eauto.
    do 2 intro; subst.
    match goal with h: ipcbv (Lam _) _ |- _ => invert h end.
    congruence. }
Qed.

Lemma reverse_star_ipcbv_preserves_stuck:
  forall t1 t2,
  star ipcbv t1 t2 ->
  stuck t2 ->
  stuck t1.
Proof.
  induction 1; eauto using reverse_ipcbv_preserves_stuck.
Qed.

Lemma reverse_ipcbv_preserves_irred:
  forall t1 t2,
  ipcbv t1 t2 ->
  irred cbv t2 ->
  irred cbv t1.
Proof.
  do 3 intro. rewrite !irred_cbv_characterization.
  intuition eauto 2 using reverse_ipcbv_preserves_stuck.
Qed.

Definition star_implication_irred_cbv :=
  star_implication (irred cbv).

Definition star_implication_reversed_irred_cbv :=
  star_implication_reversed (irred cbv).

Local Hint Resolve
  pcbv_preserves_irred
  reverse_ipcbv_preserves_irred
  star_implication_irred_cbv
  star_implication_reversed_irred_cbv
: irred.

(* -------------------------------------------------------------------------- *)

(* Strong parallel reduction requires both (1) parallel reduction; and (2) a
   decomposition as an ordinary call-by-value reduction sequence, followed
   with an internal parallel reduction step. Our goal is to prove that strong
   parallel reduction in fact coincides with parallel reduction, which means
   that this decomposition always exists. *)

Inductive spcbv : term -> term -> Prop :=
| SPCbv:
    forall t1 u t2,
    pcbv t1 t2 ->
    star cbv t1 u ->
    ipcbv u t2 ->
    spcbv t1 t2.

Local Hint Constructors spcbv : core.

(* By definition, [spcbv] is a subset of [pcbv]. *)

Lemma spcbv_subset_pcbv:
  forall t1 t2,
  spcbv t1 t2 ->
  pcbv t1 t2.
Proof.
  inversion 1; eauto.
Qed.

Local Hint Resolve spcbv_subset_pcbv : core.

(* [spcbv] is reflexive. *)

Lemma spcbv_refl:
  forall t,
  spcbv t t.
Proof.
  econstructor; eauto using red_refl with sequences obvious.
Qed.

Local Hint Resolve spcbv_refl : core.

(* -------------------------------------------------------------------------- *)

(* The main series of technical lemmas begins here. *)

Lemma crarys_lemma2:
  forall t1 t2 u1 u2,
  spcbv t1 t2 ->
  pcbv u1 u2 ->
  ~ is_value t2 ->
  spcbv (App t1 u1) (App t2 u2).
Proof.
  inversion 1; intros; subst. econstructor; obvious.
Qed.

Lemma crarys_lemma3_App:
  forall t1 t2 u1 u2,
  spcbv t1 t2 ->
  spcbv u1 u2 ->
  spcbv (App t1 u1) (App t2 u2).
Proof.
  inversion 1; inversion 1; intros; subst.
  value_or_nonvalue t2.
  { eauto 6 with obvious. }
  { eauto using crarys_lemma2. }
Qed.

Lemma crarys_lemma3_Let:
  forall t1 t2 u1 u2,
  spcbv t1 t2 ->
  pcbv u1 u2 ->
  spcbv (Let t1 u1) (Let t2 u2).
Proof.
  inversion 1; intros; subst; obvious.
Qed.

Lemma crarys_lemma4:
  forall {u1 u2},
  spcbv u1 u2 ->
  is_value u1 ->
  forall {t1 t2},
  ipcbv t1 t2 ->
  spcbv t1.[u1/] t2.[u2/].
Proof.
  induction 3; intros.
  (* Var. *)
  { destruct x as [|x]; asimpl; eauto. }
  (* Lam *)
  { rewrite !subst_lam. inv spcbv.
    econstructor; eauto 11 with sequences obvious. (* slow *) }
  (* App (nonvalue) *)
  { asimpl. eapply crarys_lemma2; obvious. eauto 9 with obvious. }
  (* App *)
  { asimpl. eapply crarys_lemma3_App; obvious. }
  (* Let *)
  { rewrite !subst_let.
    eapply crarys_lemma3_Let; eauto 12 with obvious. }
Qed.

Lemma crarys_lemma5:
  forall {t1 t2 u1 u2},
  spcbv t1 t2 ->
  spcbv u1 u2 ->
  is_value u1 ->
  spcbv t1.[u1/] t2.[u2/].
Proof.
  intros _ _ u1 u2 [ t1 t t2 Hpcbvt Hstarcbv Hipcbv ] Hpcbvu Hvalue.
  generalize (crarys_lemma4 Hpcbvu Hvalue Hipcbv).
  inversion 1; subst.
  econstructor; [| | obvious ].
  { eauto 11 with obvious. }
  { eauto using star_red_subst with sequences obvious. }
Qed.

Lemma crarys_lemma6:
  forall {t1 t2},
  pcbv t1 t2 ->
  spcbv t1 t2.
Proof.
  induction 1; try solve [ tauto ]; subst.
  (* RedParBetaV *)
  { match goal with hv: is_value _ |- _ =>
     generalize (crarys_lemma5 IHred1 IHred2 hv)
    end.
    inversion 1; subst.
    econstructor; obvious.
    eauto with sequences obvious. }
  (* RedParLetV *)
  { match goal with hv: is_value _ |- _ =>
     generalize (crarys_lemma5 IHred1 IHred2 hv)
    end.
    inversion 1; subst.
    econstructor; obvious.
    eauto with sequences obvious. }
  (* RedVar *)
  { obvious. }
  (* RedLam *)
  { clear IHred. eauto with sequences obvious. }
  (* RedAppLR *)
  { eauto using crarys_lemma3_App. }
  (* RedLetLR *)
  { eauto using crarys_lemma3_Let. }
Qed.

(* A reformulation of Lemma 6. We can now forget about [spcbv]. *)

Lemma crarys_main_lemma:
  forall t1 t2,
  pcbv t1 t2 ->
  exists t, star cbv t1 t /\ ipcbv t t2.
Proof.
  intros ? ? H.
  generalize (crarys_lemma6 H); inversion 1; subst.
  eauto.
Qed.

Lemma crarys_main_lemma_plus:
  commutation22
    cbv pcbv
    (plus cbv) ipcbv.
Proof.
  unfold commutation22. intros ? ? Hstarcbv ? Hpcbv.
  forward1 crarys_main_lemma.
  eauto with sequences.
Qed.

(* -------------------------------------------------------------------------- *)

(* Postponement. *)

Lemma crarys_lemma7:
  commutation22
    ipcbv cbv
    cbv pcbv.
Local Ltac ih7 :=
  match goal with IH: forall u, cbv _ u -> _, h: cbv _ _ |- _ =>
    generalize (IH _ h)
  end; intros (?&?&?).
Proof.
  unfold commutation22.
  induction 1; intros; subst;
  try solve [ false; eauto 2 with obvious ].
  (* IRedAppLRNonValue *)
  { invert_cbv. ih7. obvious. }
  (* IRedAppLR *)
  { (* [t1] and [t2] are values. *)
    clear IHipcbv1.
    invert_cbv.
    (* Case: [u1] and [u2] are values. (Case 5 in Crary's proof.) *)
    { assert (is_value u1). { obvious. }
      match goal with h: ipcbv _ (Lam _) |- _ => invert h end.
      eexists; split.
      { eapply RedBetaV; obvious. }
      { eauto 7 with obvious. }
    }
    (* Case: [u1] and [u2] are nonvalues. (Case 4 in Crary's proof.) *)
    { ih7. eexists; split; obvious. }
  }
  (* IRedLetLR *)
  { invert_cbv.
    (* Case: [t1] and [t2] are values. *)
    { eexists; split; eauto 8 with obvious. }
    (* Case: [t1] and [t2] are nonvalues. *)
    { ih7. eexists; split; obvious. }
  }
Qed.

(* Internal parallel reduction commutes with reduction, as follows. *)

Lemma crarys_lemma8_plus:
  commutation22
    ipcbv cbv
    (plus cbv) ipcbv.
Proof.
  eauto using crarys_lemma7, crarys_main_lemma_plus,
              commutation22_transitive.
Qed.

Lemma crarys_lemma8:
  commutation22
    ipcbv cbv
    (star cbv) ipcbv.
Proof.
  eauto using crarys_lemma8_plus, commutation22_variance with sequences.
Qed.

Lemma crarys_lemma8b_plus:
  commutation22
    ipcbv (plus cbv)
    (plus cbv) ipcbv.
Proof.
  eauto using commute_R_Splus, crarys_lemma8_plus.
Qed.

Lemma crarys_lemma8b:
  commutation22
    ipcbv (star cbv)
    (star cbv) ipcbv.
Proof.
  eauto using commute_R_Sstar, crarys_lemma8.
Qed.

Lemma crarys_lemma8b_plus_star:
  commutation22
    (star ipcbv) (plus cbv)
    (plus cbv) (star ipcbv).
Proof.
  eapply commute_Rstar_Splus.
  eauto using crarys_lemma8b_plus, commutation22_variance with sequences.
Qed.

(* -------------------------------------------------------------------------- *)

(* Bifurcation. *)

(* A sequence of parallel reduction steps can be reformulated as a sequence
   of ordinary reduction steps, followed with a sequence of internal parallel
   reduction steps. *)

Lemma crarys_lemma9:
  forall t1 t2,
  star pcbv t1 t2 ->
  exists t,
  star cbv t1 t /\ star ipcbv t t2.
Proof.
  induction 1.
  { eauto with sequences. }
  { unpack.
    forward1 crarys_main_lemma.
    forward2 crarys_lemma8b.
    eauto with sequences. }
Qed.

(* The following result does not seem to explicitly appear in Crary's paper. *)

Lemma pcbv_cbv_commutation1:
  commutation22
    (star pcbv) cbv
    (plus cbv) (star pcbv).
Proof.
  intros t1 t2 ? t3 ?.
  forward1 crarys_lemma9.
  assert (plus cbv t2 t3). { eauto with sequences. }
  forward2 crarys_lemma8b_plus_star.
  eauto 6 using ipcbv_subset_pcbv, star_covariant with sequences.
Qed.

Lemma pcbv_cbv_commutation:
  commutation22
    (star pcbv) (plus cbv)
    (plus cbv) (star pcbv).
Proof.
  eauto using pcbv_cbv_commutation1, commute_R_Splus.
Qed.

(* -------------------------------------------------------------------------- *)

(* The notion of "reducing (in zero or more steps) to a value" is the same
   under [pcbv] and under [cbv]. *)

Lemma equiconvergence:
  forall t v,
  star pcbv t v ->
  is_value v ->
  exists v',
  star cbv t v' /\ is_value v'.
Proof.
  intros. forward1 crarys_lemma9. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* "Adequacy of reduction". In Crary's terminology, "reduction" is the
   compatible closure of "evaluation", and "evaluation" is [cbv]. A
   relation is adequate iff it is contained in contextual equivalence. *)

(* The adequacy theorem. (Crary's lemma 10.) *)

Theorem pcbv_adequacy:
  forall t1 t2,
  star pcbv t1 t2 ->
  (halts cbv t1) <-> (halts cbv t2).
Proof.
  split.
  (* Case: [t1] reduces to an irreducible term [u1]. *)
  { intros (u1&?&?).
    (* [t1] reduces via [pcbv*] to both [u1] and [t2], so they must both
       reduce via [pcbv*] to some common term [u]. *)
    assert (star pcbv t1 u1). { eauto using star_covariant, cbv_subset_pcbv. }
    forward2 diamond_star_pcbv.
    (* The reduction of [t2] to [u] can be bifurcated. That is, [t2] first
       reduces via [cbv*], then via [ipbcv], to [u]. *)
    forward1 crarys_lemma9.
    (* Because [pcbv] and [ipcbv] (reversed) both preserve irreducibility,
       this establishes that [t2] halts. *)
    eexists. split; eauto with irred.
  }
  (* Case: [t2] reduces to an irreducible term [u2]. *)
  { intros (u2&?&?).
    (* Therefore, [t1] reduces via [pcbv*] to [u2]. *)
    assert (star pcbv t1 u2).
    { eauto using cbv_subset_pcbv, star_covariant with sequences. }
    (* This reduction can be bifurcated. That is, [t1] first reduces via
       [cbv*], then via [ipcbv], to [u2]. *)
    forward1 crarys_lemma9.
    (* Because [ipcbv] (reversed) preserves irreducibility, this proves
       that [t1] halts. *)
    eexists. split; eauto with irred.
  }
Qed.

(* The previous result implies that [pcbv] and [star pcbv] are contained in
   contextual equivalence. We do not establish this result, because we do
   not need it, and we have not defined contextual equivalence. *)

(* -------------------------------------------------------------------------- *)

(* Preservation of divergence. *)

(* If we have an infinite [cbv] reduction sequence with [pcbv] steps in it,
   then we have an infinite [cbv] reduction sequence. *)

Lemma pcbv_preserves_divergence:
  forall t,
  infseq (composition (plus cbv) pcbv) t ->
  infseq cbv t.
Proof.
  intros ? Hinfseq.
  (* We generalize the statement slightly by allowing any number of initial
     [pcbv] steps from [t] to [u] before finding an infinite reduction sequence
     out of [u]. *)
  eapply infseq_coinduction_principle with (P := fun t =>
    exists u, star pcbv t u /\ infseq (composition (plus cbv) pcbv) u
  ); [| eauto with sequences ].
  (* We have to show that, under this hypothesis, we are able to take one step
     of [cbv] out of [t] and reach a term that satisfies this hypothesis again. *)
  clear dependent t. intros t (u&?&hInfSeq).
  pick infseq invert.
  pick @composition invert. unpack.
  (* Out of [t], we have [pcbv* . cbv+ . pcbv ...]. *)
  (* Thus,       we have [cbv+ . pcbv* . pcbv ...]. *)
  forward2 pcbv_cbv_commutation.
  (* Thus,       we have [cbv  . pcbv*        ...]. *)
  pick plus invert.
  (* We are happy. *)
  eexists. split; [ eauto |].
  eexists. split; [| eauto ].
  eauto 6 using cbv_subset_pcbv, star_covariant with sequences.
Qed.

(* -------------------------------------------------------------------------- *)

(* The final result in Crary's paper is a standardization theorem for
   call-by-value reduction. The theorem states that any sequence of parallel
   reduction steps can be put in a "standard" form, as defined by the relation
   [stdred] below. *)

Inductive stdred : term -> term -> Prop :=
| StdNil:
    forall t,
    stdred t t
| StdCons:
    forall t1 t2 t3,
    cbv t1 t2 ->
    stdred t2 t3 ->
    stdred t1 t3
| StdLam:
    forall t1 t2,
    stdred t1 t2 ->
    stdred (Lam t1) (Lam t2)
| StdApp:
    forall t1 t2 u1 u2,
    stdred t1 u1 ->
    stdred t2 u2 ->
    stdred (App t1 t2) (App u1 u2)
| StdLet:
    forall t1 t2 u1 u2,
    stdred t1 u1 ->
    stdred t2 u2 ->
    stdred (Let t1 t2) (Let u1 u2)
.

Hint Constructors stdred : stdred.

(* A couple of more flexible constructors for [stdred]. *)

Lemma star_cbv_subset_stdred:
  forall t1 t2,
  star cbv t1 t2 ->
  stdred t1 t2.
Proof.
  induction 1; eauto with stdred.
Qed.

Lemma StdConsStar:
  forall t1 t2 t3,
  star cbv t1 t2 ->
  stdred t2 t3 ->
  stdred t1 t3.
Proof.
  induction 1; eauto with stdred.
Qed.

Hint Resolve star_cbv_subset_stdred StdConsStar : stdred.

(* The following lemma analyzes a reduction sequence of the form [star ipcbv
   t1 t2], where the head constructor of the term [t2] is known. In every
   case, it can be concluded that the term [t1] exhibits the same head
   constructor as [t2]. *)

Lemma star_ipcbv_into:
  forall t1 t2,
  star ipcbv t1 t2 ->
  match t2 with
  | Var x =>
      t1 = Var x
  | Lam u2 =>
      exists u1, t1 = Lam u1 /\ star pcbv u1 u2
  |  App t21 t22 =>
      exists t11 t12,
      t1 = App t11 t12 /\ star pcbv t11 t21 /\ star pcbv t12 t22
  | Let t21 t22 =>
      exists t11 t12,
      t1 = Let t11 t12 /\ star ipcbv t11 t21 /\ star pcbv t12 t22
  end.
Proof.
  (* By induction on the reduction sequence. *)
  induction 1; intros; subst.
  (* Case: [star_refl]. By cases on [t2]. *)
  { match goal with t: term |- _ => destruct t end;
    eauto with sequences. }
  (* Case: [star_step]. By cases on [t2], then by examination of
     the [ipcbv] step. *)
  { match goal with t: term |- _ => destruct t end; unpack; inv ipcbv;
    eauto 9 using ipcbv_subset_pcbv with sequences. }
Qed.

(* The standardization theorem. (Crary's lemma 12.) *)

Theorem cbv_standardization:
  forall t2 t1,
  star pcbv t1 t2 ->
  stdred t1 t2.
Proof.
  induction t2; intros;
  forward1 crarys_lemma9;
  forward star_ipcbv_into;
  eauto 8 using ipcbv_subset_pcbv, star_covariant with stdred.
Qed.
