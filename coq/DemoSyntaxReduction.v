Require Import Autosubst.Autosubst.

(* This file is intended as a mini-demonstration of:
   1. defining the syntax of a calculus, in de Bruijn's representation;
   2. equipping it with an operational semantics;
   3. proving a basic lemma, e.g.,
      stability of the semantics under substitution. *)

(* -------------------------------------------------------------------------- *)

(* The syntax of the lambda-calculus. *)

Inductive term :=
| Var:          var -> term
| Lam:  {bind term} -> term
| App: term -> term -> term
.

(* -------------------------------------------------------------------------- *)

(* The following incantations let [AutoSubst] work its magic for us.
   We obtain, for free, the operations of de Bruijn algebra: application
   of a substitution to a term, composition of substitutions, etc. *)

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(* -------------------------------------------------------------------------- *)

(* A demo of the tactics [autosubst] and [asimpl]. *)

Goal
  forall sigma,
  (Lam (App (Var 0) (Var 1))).[sigma] =
   Lam (App (Var 0) (sigma 0).[ren (+1)]).
Proof.
  intros.
  (* The two sides of this equation are distinct terms: the built-in
     tactic [reflexivity] cannot prove this equation. *)
  Fail reflexivity.
  (* The tactic [autosubst] is able to prove this equality. *)
  autosubst.
Restart.
  intros.
  (* Another way of proceeding is to first simplify the goal using [asimpl]. *)
  asimpl.
  (* [ids], the identity substitution, maps 0 to [Var 0], 1 to [Var 1],
     and so on, so it is really equal to [Var] itself. As a result, the
     built-in tactic [reflexivity] proves this simplified equation. *)
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* More demos: let us check that the laws of substitution are satisfied. *)

Lemma subst_var:
  forall x sigma,
  (Var x).[sigma] = sigma x.
Proof.
  autosubst.
Qed.

Lemma subst_lam:
  forall t sigma,
  (Lam t).[sigma] = Lam (t.[up sigma]).
Proof.
  autosubst.
Qed.

Lemma subst_app:
  forall t1 t2 sigma,
  (App t1 t2).[sigma] = App t1.[sigma] t2.[sigma].
Proof.
  autosubst.
Qed.

(* A reminder of the meaning of [up sigma]. *)

Lemma up_def:
  forall sigma,
  up sigma = Var 0 .: (sigma >> ren (+1)).
Proof.
  intros. autosubst.
Qed.

(* -------------------------------------------------------------------------- *)

(* A small-step reduction semantics. *)

(* This is a relation between terms: hence, its type is [term -> term -> Prop].
   It is inductively defined by three inference rules, as follows: *)

Inductive red : term -> term -> Prop :=

(* Beta-reduction. The use of an explicit equality hypothesis is a technical
   convenience. We could instead write [red (App (Lam t1) t2) t1.[t2/]] in
   the conclusion, and remove the auxiliary variable [u], but that would make
   it more difficult for Coq to apply the inference rule [RedBeta]. Using an
   explicit equality premise makes the rule more widely applicable. Of course
   the user still has to prove (after applying the rule) that the equality
   holds. *)
| RedBeta:
    forall t1 t2 u,
    t1.[t2/] = u ->
    red (App (Lam t1) t2) u

(* Reduction in the left-hand side of an application. *)
| RedAppL:
    forall t1 t2 u,
    red t1 t2 ->
    red (App t1 u) (App t2 u)

(* Reduction in the right-hand side of an application. *)
| RedAppR:
    forall t u1 u2,
    red u1 u2 ->
    red (App t u1) (App t u2)
.

(* The following means that [eauto with red] is allowed to apply the above
   three inference rules. *)

Hint Constructors red : red.

(* No strategy is built into this reduction relation: it is not restricted to
   call-by-value or call-by-name. It is nondeterministic. Only weak reduction
   is permitted here: we have not allowed reduction under a [Lam]. These choices
   are arbitrary: this is just a demo anyway. *)

(* -------------------------------------------------------------------------- *)

(* This incantation means that [eauto with autosubst] can use the tactic
   [autosubst] to prove an equality. It is used in the last "expert" proof
   of the lemma [red_subst] below.  *)

Hint Extern 1 (_ = _) => autosubst : autosubst.

(* -------------------------------------------------------------------------- *)

(* Demo: a term that reduces to itself. *)

Definition Delta :=
  Lam (App (Var 0) (Var 0)).

Definition Omega :=
  App Delta Delta.

Goal
  red Omega Omega.
Proof.
  (* Apply the beta-reduction rule.
     (This forces Coq to unfold the left-hand [Omega].) *)
  eapply RedBeta.
  (* Check this equality. *)
  asimpl. (* optional *)
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* Let us prove that the semantics is stable under arbitrary substitutions. *)

Lemma red_subst:
  forall t1 t2,
  red t1 t2 ->
  forall sigma,
  red t1.[sigma] t2.[sigma].
Proof.

  (* We attack a proof by induction on the derivation of [red t1 t2]. *)
  induction 1; intros.
  (* Case: [RedBeta]. *)
  { subst u.
    asimpl.
    eapply RedBeta.
    (* Wow -- we have to prove a complicated-looking commutation property
       of substitutions. Fortunately, [autosubst] is here for us! *)
    autosubst. }
  (* Case: [RedAppL]. The proof can be done slowly, in three steps:
     1. push the substitution into [App];
     2. apply the rule [RedAppL]; a simpler subgoal remains to be proved;
     3. apply the induction hypothesis, which proves this subgoal. *)
  { asimpl.
    eapply RedAppL.
    eapply IHred. }
  (* Case: [RedAppR]. The proof could be done using the same three steps
     as above, but one can also let the last two steps be automatically
     found by [eauto]. *)
  { asimpl. eauto using red. }
  (* The proof is now finished. *)

  (* For the fun of it, let us do the proof again in a more "expert" style. *)
Restart.
  (* The proof is still by induction. All three cases begin in the same way,
     so this common pattern can be shared, as follows. We use the semicolon
     which in Ltac has special meaning: when one writes [command1; command2],
     [command1] can produce multiple subgoals, and [command2] is applied to
     every subgoal (in parallel). Thus, here, in each of the three cases,
     we perform the sequence of commands [intros; subst; asimpl; econstructor].
     The effect of [econstructor] is to apply one of [RedBeta], [RedAppL] and
     [RedAppR] -- whichever is applicable. *)
  induction 1; intros; subst; asimpl; econstructor.
  (* Then, the three subgoals can be finished as follows: *)
  { autosubst. }
  { eauto. }
  { eauto. }
  (* The proof is now finished (again). *)

  (* For the fun of it, let us redo the proof in an even more expert style.
     We remark that each of the three subgoals can be proved by [eauto with
     autosubst], so we can write a fully shared command, where the subgoals
     are no longer distinguished: *)
Restart.
  induction 1; intros; subst; asimpl; econstructor; eauto with autosubst.
  (* Actually, [asimpl] on the previous line seems not even needed. *)
  (* The proof is now finished (yet again). *)

  (* There are several lessons that one can draw from this demo:

     1. The machine helps us by keeping track of what we may assume
        and what we have to prove.

     2. There are several ways in which a proof can be written. In the
        beginning, it is advisable to write a step-by-step, simple-minded
        proof; later on, when the proof is finished and well-understood,
        it can be revisited for greater compactness and sharing.

     3. The proof of this lemma *can* fit in one line. On paper, one
        would say that the proof is "by induction" and "immediate".
        Here, we are able to be almost as concise, yet we have much
        greater confidence.

     4. The point of the "expert" proof is not just to make the proof
        more concise: the point is also to make the proof more robust
        in the face of future evolution. For instance, as an EXERCISE,
        extend the calculus with pairs and projections, and see how the
        proof scripts must be extended. You should find that the last
        "expert" proof above requires no change at all!

  *)

Qed.

(* -------------------------------------------------------------------------- *)

(* As another EXERCISE, extend the operational semantics with a rule that
   allows strong reduction, that is, reduction under a lambda-abstraction.
   This exercise is more difficult; do not hesitate to ask for help or hints. *)

(* Another suggested EXERCISE: define call-by-value reduction, [cbv]. Prove
   that [cbv] is a subset of [red]. Prove that values do not reduce. Prove
   that [cbv] is deterministic. *)
