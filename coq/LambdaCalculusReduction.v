Require Import MyTactics.
Require Import Sequences.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusFreeVars.

(* We give a symbolic name to each reduction rule. *)

Inductive rule :=
| RuleBetaV    (* reduction of a beta-v redex: (\x.t) v                   *)
| RuleLetV     (* reduction of a let-v redex:  let x = v in t             *)
| RuleBeta     (* reduction of a beta   redex: (\x.t) u                   *)
| RuleLet      (* reduction of a let redex:    let x = u in t             *)
| RuleParBetaV (* reduction of a beta-v redex and reduction in both sides *)
| RuleParLetV  (* reduction of a let redex and reduction in both sides    *)
| RuleVar      (* no reduction                                            *)
| RuleLam      (* reduction in [Lam _]                                    *)
| RuleAppL     (* reduction in [App _ u]                                  *)
| RuleAppVR    (* reduction in [App v _], if [v] is a value               *)
| RuleAppLR    (* reduction in both sides of [App _ _]                    *)
| RuleLetL     (* reduction in [Let _ u]                                  *)
| RuleLetR     (* reduction in [Let t _]                                  *)
| RuleLetLR    (* reduction in both sides of [Let _ _]                    *).

(* A mask is a set of rules. *)

Definition mask :=
  rule -> Prop.

(* A generic small-step reduction semantics, parameterized with a mask. *)

Inductive red (mask : mask) : term -> term -> Prop :=
| RedBetaV:
    forall t v u,
    mask RuleBetaV ->
    is_value v ->
    t.[v/] = u ->
    red mask (App (Lam t) v) u
| RedLetV:
    forall t v u,
    mask RuleLetV ->
    is_value v ->
    t.[v/] = u ->
    red mask (Let v t) u
| RedBeta:
    forall t1 t2 u,
    mask RuleBeta ->
    t1.[t2/] = u ->
    red mask (App (Lam t1) t2) u
| RedLet:
    forall t1 t2 u,
    mask RuleLet ->
    t2.[t1/] = u ->
    red mask (Let t1 t2) u
| RedParBetaV:
    forall t1 v1 t2 v2 u,
    mask RuleParBetaV ->
    is_value v1 ->
    red mask t1 t2 ->
    red mask v1 v2 ->
    t2.[v2/] = u ->
    red mask (App (Lam t1) v1) u
| RedParLetV:
    forall t1 t2 v1 v2 u,
    mask RuleParLetV ->
    is_value v1 ->
    red mask t1 t2 ->
    red mask v1 v2 ->
    t2.[v2/] = u ->
    red mask (Let v1 t1) u
| RedVar:
    forall x,
    mask RuleVar ->
    red mask (Var x) (Var x)
| RedLam:
    forall t1 t2,
    mask RuleLam ->
    red mask t1 t2 ->
    red mask (Lam t1) (Lam t2)
| RedAppL:
    forall t1 t2 u,
    mask RuleAppL ->
    red mask t1 t2 ->
    red mask (App t1 u) (App t2 u)
| RedAppVR:
    forall v u1 u2,
    mask RuleAppVR ->
    is_value v ->
    red mask u1 u2 ->
    red mask (App v u1) (App v u2)
| RedAppLR:
    forall t1 t2 u1 u2,
    mask RuleAppLR ->
    red mask t1 t2 ->
    red mask u1 u2 ->
    red mask (App t1 u1) (App t2 u2)
| RedLetL:
    forall t1 t2 u,
    mask RuleLetL ->
    red mask t1 t2 ->
    red mask (Let t1 u) (Let t2 u)
| RedLetR:
    forall t u1 u2,
    mask RuleLetR ->
    red mask u1 u2 ->
    red mask (Let t u1) (Let t u2)
| RedLetLR:
    forall t1 t2 u1 u2,
    mask RuleLetLR ->
    red mask t1 t2 ->
    red mask u1 u2 ->
    red mask (Let t1 u1) (Let t2 u2)
.

Hint Constructors red : red obvious.

(* The following mask defines the call-by-value reduction semantics. *)

Definition cbv_mask rule :=
  match rule with
  | RuleBetaV    (* reduction of a beta-v redex: (\x.t) v                 *)
  | RuleLetV     (* reduction of a let-v redex:  let x = v in t           *)
  | RuleAppL     (* reduction in [App _ u]                                *)
  | RuleAppVR    (* reduction in [App v _], if [v] is a value             *)
  | RuleLetL     (* reduction in [Let _ u]                                *)
      => True
  | _ => False
  end.

Notation cbv := (red cbv_mask).

(* The following mask defines the call-by-name reduction semantics. *)

Definition cbn_mask rule :=
  match rule with
  | RuleBeta     (* reduction of a beta   redex: (\x.t) v                 *)
  | RuleLet      (* reduction of a let redex:    let x = v in t           *)
  | RuleAppL     (* reduction in [App _ u]                                *)
      => True
  | _ => False
  end.

Notation cbn := (red cbn_mask).

(* The parallel by-value reduction semantics allows beta-v reductions under
   arbitrary contexts, including under lambda-abstractions. Furthermore, it
   allows parallel reductions (and allows no reduction at all). *)

Definition pcbv_mask rule :=
  match rule with
  | RuleParBetaV (* reduction of a beta redex and reduction in both sides *)
  | RuleParLetV  (* reduction of a let redex and reduction in both sides  *)
  | RuleVar      (* no reduction                                          *)
  | RuleLam      (* reduction in [Lam _]                                  *)
  | RuleAppLR    (* reduction in both sides of [App _ _]                  *)
  | RuleLetLR    (* reduction in both sides of [Let _ _]                  *)
      => True
  | _ => False
  end.

Notation pcbv := (red pcbv_mask).

(* The tactic [obvious] should be able to prove goals of the form
   [red mask t1 t2], where [mask] is a known mask. *)

Hint Extern 1 (cbv_mask _)  => (simpl; tauto) : red obvious.
Hint Extern 1 (cbn_mask _)  => (simpl; tauto) : red obvious.
Hint Extern 1 (pcbv_mask _) => (simpl; tauto) : red obvious.

Goal cbv (Let (App (Lam (Var 0)) (Var 0)) (Var 0)) (Let (Var 0) (Var 0)).
Proof. obvious. Qed.

Goal cbv (Let (Var 0) (Var 0)) (Var 0).
Proof. obvious. Qed.

Goal cbn (Let (Var 0) (Var 0)) (Var 0).
Proof. obvious. Qed.

Goal
  let id := Lam (Var 0) in
  let t := (Let (Lam (Var 0)) (Var 0)) in
  cbn (App id t) t.
Proof. simpl. obvious. Qed.

Goal pcbv (App (App (Lam (Var 0)) (Var 0)) (App (Lam (Var 0)) (Var 0)))
          (App (Var 0) (Var 0)).
Proof.
  eauto 8 with obvious.
Qed.

(* The tactic [step] applies to a goal of the form [star (red mask) t1 t2]. It
   causes the term [t1] to take one step of reduction towards [t1'], turning
   the goal into [star (red mask) t1' t2]. *)

Ltac step :=
  eapply star_step; [ obvious |].

(* The tactic [finished] applies to a goal of the form [star (red mask) t1 t2].
   It turns the goal into [t1 = t2]. *)

Ltac finished :=
  eapply star_refl_eq.

(* The tactic [invert_cbv] inverts a hypothesis of the form [cbv t1 t2]. *)

Ltac invert_cbv :=
  pick (red cbv_mask) invert;
  try solve [ false; eauto 3 with obvious ].

Ltac invert_star_cbv :=
  pick (star cbv) invert.

Ltac invert_cbn :=
  pick (red cbn_mask) invert;
  try solve [ false; eauto 3 with obvious ].

(* If the following four rules are enabled, then reduction is reflexive. *)

Lemma red_refl:
  forall mask : mask,
  mask RuleVar ->
  mask RuleLam ->
  mask RuleAppLR ->
  mask RuleLetLR ->
  forall t,
  red mask t t.
Proof.
  induction t; eauto with red.
Qed.

(* [RuleBetaV] and [RuleLetV] are special cases of [RuleParBetaV] and
   [RuleParLetV], hence are admissible in parallel call-by-value reduction. *)

Lemma pcbv_RedBetaV:
  forall t v u,
  is_value v ->
  t.[v/] = u ->
  pcbv (App (Lam t) v) u.
Proof.
  eauto using red_refl with obvious.
Qed.

Lemma pcbv_RedLetV:
  forall t v u,
  is_value v ->
  t.[v/] = u ->
  pcbv (Let v t) u.
Proof.
  eauto using red_refl with obvious.
Qed.

(* Sequences of reduction, [star cbv], can be carried out under a context. *)

Lemma star_cbv_AppL:
  forall t1 t2 u,
  star cbv t1 t2 ->
  star cbv (App t1 u) (App t2 u).
Proof.
  induction 1; eauto with sequences obvious.
Qed.

Lemma star_pcbv_AppL:
  forall t1 t2 u,
  star pcbv t1 t2 ->
  star pcbv (App t1 u) (App t2 u).
Proof.
  induction 1; eauto using red_refl with sequences obvious.
Qed.

Lemma plus_pcbv_AppL:
  forall t1 t2 u,
  plus pcbv t1 t2 ->
  plus pcbv (App t1 u) (App t2 u).
Proof.
  induction 1.
  econstructor; [ | eauto using star_pcbv_AppL ].
  eapply RedAppLR; eauto using red_refl with obvious.
Qed.

Lemma star_cbv_AppR:
  forall t u1 u2,
  is_value t ->
  star cbv u1 u2 ->
  star cbv (App t u1) (App t u2).
Proof.
  induction 2; eauto with sequences obvious.
Qed.

Hint Resolve star_cbv_AppL star_pcbv_AppL plus_pcbv_AppL star_cbv_AppR : red obvious.

Lemma star_cbv_AppLR:
  forall t1 t2 u1 u2,
  star cbv t1 t2 ->
  star cbv u1 u2 ->
  is_value t2 ->
  star cbv (App t1 u1) (App t2 u2).
Proof.
  eauto with sequences obvious.
Qed.

Lemma star_cbv_LetL:
  forall t1 t2 u,
  star cbv t1 t2 ->
  star cbv (Let t1 u) (Let t2 u).
Proof.
  induction 1; eauto with sequences obvious.
Qed.

Hint Resolve star_cbv_AppLR star_cbv_LetL : red obvious.

(* Reduction commutes with substitutions of values for variables. (This
   includes renamings.) This is true of every reduction strategy, with
   the proviso that if [RuleVar] is enabled, then [RuleLam], [RuleAppLR]
   and [RuleLetLR] must be enabled as well, so that reduction is reflexive. *)

Lemma red_subst:
  forall mask : mask,
  (mask RuleVar -> mask RuleLam) ->
  (mask RuleVar -> mask RuleAppLR) ->
  (mask RuleVar -> mask RuleLetLR) ->
  forall t1 t2,
  red mask t1 t2 ->
  forall sigma,
  is_value_subst sigma ->
  red mask t1.[sigma] t2.[sigma].
Proof.
  induction 4; simpl; intros; subst;
  try solve [ econstructor; solve [ eauto with is_value | autosubst ]].
  (* Case: [Var] *)
  { eauto using red_refl. }
Qed.

Lemma star_red_subst:
  forall mask : mask,
  (mask RuleVar -> mask RuleLam) ->
  (mask RuleVar -> mask RuleAppLR) ->
  (mask RuleVar -> mask RuleLetLR) ->
  forall t1 t2 sigma,
  star (red mask) t1 t2 ->
  is_value_subst sigma ->
  star (red mask) t1.[sigma] t2.[sigma].
Proof.
  induction 4; eauto using red_subst with sequences.
Qed.

(* Call-by-value reduction is contained in parallel call-by-value. *)

Lemma cbv_subset_pcbv:
  forall t1 t2,
  cbv t1 t2 ->
  pcbv t1 t2.
Proof.
  induction 1; try solve [ tauto ]; eauto using red_refl with red.
Qed.

(* Under call-by-value, values do not reduce. *)

Lemma values_do_not_reduce:
  forall t1 t2,
  cbv t1 t2 ->
  ~ is_value t1.
Proof.
  inversion 1; is_value.
Qed.

Hint Resolve values_do_not_reduce : is_value obvious.

Hint Extern 1 (False) => (eapply values_do_not_reduce) : is_value obvious.

Lemma is_value_irred:
  forall v,
  is_value v ->
  irred cbv v.
Proof.
  intros. intro. obvious.
Qed.

Hint Resolve is_value_irred : irred obvious.

(* Under every strategy, the property of being a value is preserved by
   reduction. *)

Lemma values_are_stable:
  forall mask v1 v2,
  red mask v1 v2 ->
  is_value v1 ->
  is_value v2.
Proof.
  induction 1; is_value.
Qed.

Lemma nonvalues_are_stable:
  forall mask v1 v2,
  red mask v1 v2 ->
  ~ is_value v2 ->
  ~ is_value v1.
Proof.
  induction 1; is_value.
Qed.

Hint Resolve values_are_stable nonvalues_are_stable : is_value obvious.

(* [cbv] is deterministic. *)

Lemma cbv_deterministic:
  forall t t1,
  cbv t t1 ->
  forall t2,
  cbv t t2 ->
  t1 = t2.
Proof.
  (* Induction over [cbv t t1]. *)
  induction 1; try solve [ tauto ]; intros; subst;
  (* Invert the second hypothesis, [cbv t t2]. The fact that values do not
     reduce is used to eliminate some cases. *)
  invert_cbv;
  (* The result follows. *)
  f_equal; eauto.
Qed.

(* Inversion lemmas for [irred]. *)

Lemma invert_irred_cbv_App_1:
  forall t u,
  irred cbv (App t u) ->
  irred cbv t.
Proof.
  intros. eapply irred_irred; obvious.
Qed.

Lemma invert_irred_cbv_App_2:
  forall t u,
  irred cbv (App t u) ->
  is_value t ->
  irred cbv u.
Proof.
  intros. eapply irred_irred; obvious.
Qed.

Lemma invert_irred_cbv_App_3:
  forall t u,
  irred cbv (App t u) ->
  is_value t ->
  is_value u ->
  forall t', t <> Lam t'.
Proof.
  intros ? ? Hirred. repeat intro. subst.
  eapply Hirred. obvious.
Qed.

Lemma invert_irred_cbv_Let_1:
  forall t u,
  irred cbv (Let t u) ->
  irred cbv t.
Proof.
  intros. eapply irred_irred; obvious.
Qed.

Lemma invert_irred_cbv_Let_2:
  forall t u,
  irred cbv (Let t u) ->
  ~ is_value t.
Proof.
  intros ? ? Hirred ?. eapply Hirred. obvious.
Qed.

Hint Resolve
  invert_irred_cbv_App_1
  invert_irred_cbv_App_2
  invert_irred_cbv_Let_1
  invert_irred_cbv_Let_2
: irred.

(* An analysis of irreducible terms for call-by-value reduction. A stuck
   term is either an application [v1 v2] where [v1] is not a function or
   a stuck term in an evaluation context. *)

Inductive stuck : term -> Prop :=
| StuckApp:
    forall v1 v2,
    is_value v1 ->
    is_value v2 ->
    (forall t, v1 <> Lam t) ->
    stuck (App v1 v2)
| StuckAppL:
    forall t u,
    stuck t ->
    stuck (App t u)
| StuckAppR:
    forall v u,
    is_value v ->
    stuck u ->
    stuck (App v u)
| StuckLetL:
    forall t u,
    stuck t ->
    stuck (Let t u).

Hint Constructors stuck : stuck.

(* To go wrong is to reduce to a stuck term. *)

Definition goes_wrong t :=
  exists t', star cbv t t' /\ stuck t'.

(* A stuck term cannot be a value. *)

Lemma stuck_nonvalue:
  forall t,
  stuck t ->
  ~ is_value t.
Proof.
  induction 1; is_value.
Qed.

(* Every stuck term is irreducible. *)

Ltac prove_irred_cbv :=
  do 2 intro; invert_cbv.

Lemma stuck_irred:
  forall t,
  stuck t ->
  irred cbv t.
Proof.
  induction 1; prove_irred_cbv; try solve [
    eauto using irreducible_terms_do_not_reduce
  | eapply stuck_nonvalue; obvious
  ].
  (* StuckApp *)
  { congruence. }
Qed.

Hint Resolve stuck_irred : irred obvious.

(* Every irreducible term either is a value or is stuck. *)

Lemma irred_cbv_is_value_or_stuck:
  forall t,
  irred cbv t ->
  is_value t \/ stuck t.
Proof.
  induction t; intro Hirred;
  try solve [ is_value ]; right.
  (* App *)
  { assert (H1: irred cbv t1). { eauto with irred. }
    destruct (IHt1 H1); [| eauto with stuck ].
    assert (H2: irred cbv t2). { eauto with irred. }
    destruct (IHt2 H2); [| eauto with stuck ].
    eapply StuckApp; eauto using invert_irred_cbv_App_3. }
  (* Let *)
  { assert (H: irred cbv t). { eauto with irred. }
    destruct (IHt H); [| eauto with stuck ].
    assert (~ is_value t). { eauto with irred. }
    tauto. }
Qed.

(* The converse is true as well. *)

Lemma irred_cbv_characterization:
  forall t,
  irred cbv t <->
  is_value t \/ stuck t.
Proof.
  split.
  { eauto using irred_cbv_is_value_or_stuck. }
  { intuition eauto with irred. }
Qed.

(* A closed value must be a lambda-abstraction. *)

Lemma closed_value:
  forall v,
  is_value v ->
  closed v ->
  exists t, v = Lam t.
Proof.
  intros. destruct v as [| t | | ]; try solve [ false; is_value ].
  { false. eapply closed_Var. eauto. }
  { exists t. eauto. }
Qed.

(* A stuck term cannot be closed. *)

Lemma stuck_closed:
  forall t,
  stuck t ->
  closed t ->
  False.
Proof.
  induction 1; intros; eauto with closed.
  (* StuckApp *)
  { assert (ht1: exists t1, v1 = Lam t1).
    { eauto using closed_value with closed. }
    destruct ht1 as (?&?). subst v1. congruence. }
Qed.

(* Under call-by-value, every closed term either reduces or is a value. *)

Lemma cbv_progress:
  forall t,
  closed t ->
  is_value t \/ exists u, cbv t u.
Local Ltac ih IH :=
  destruct IH as [| [ ? ? ]]; [ eauto with closed | | obvious ].
Proof.
  (* We give a direct proof, but the result also follows from
     [irred_cbv_is_value_or_stuck] and [stuck_closed]. *)
  induction t as [| | t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2 ];
  try solve [ left; obvious ]; right.
  (* App *)
  { ih IHt1.
    ih IHt2.
    destruct (closed_value t1) as [ u1 ? ]; eauto with closed; subst t1.
    obvious.
  }
  (* Let *)
  { ih IHt1. obvious. }
Qed.
