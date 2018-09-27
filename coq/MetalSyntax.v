Require Import List.
Require Import MyList.
Require Import MyTactics.
Require Export Autosubst.Autosubst.
Require Export AutosubstExtra.
Require Export Autosubst_EOS.
Require Export Autosubst_FreeVars.

(* -------------------------------------------------------------------------- *)

(* Metal is a lambda-calculus where every lambda-abstraction must be closed.
   It is equipped with pairs and projections. It is intended to serve as the
   target of closure conversion. *)

(* -------------------------------------------------------------------------- *)

(* Syntax. *)

Inductive metal :=
| MVar  : var -> metal
| MLam  : {bind metal} -> metal
| MApp  : metal -> metal -> metal
| MLet  : metal -> {bind metal} -> metal
| MPair : metal -> metal -> metal
| MPi   : nat -> metal -> metal
.

Instance Ids_metal : Ids metal. derive. Defined.
Instance Rename_metal : Rename metal. derive. Defined.
Instance Subst_metal : Subst metal. derive. Defined.
Instance SubstLemmas_metal : SubstLemmas metal. derive. Qed.

Instance IdsLemmas_metal : IdsLemmas metal.
Proof. econstructor. intros. injections. eauto. Qed.

(* -------------------------------------------------------------------------- *)

(* We equip the calculus with pairs, instead of general tuples, because
   this makes life in Coq simpler -- we would otherwise have an occurrence
   of [list metal] in the definition of [metal], and would need to ask for
   a custom induction scheme. *)

(* Instead, we simulate tuples using nested pairs. This would of course be
   inefficient in real life, but fur our purposes, should be fine. *)

Fixpoint MTuple ts :=
  match ts with
  | nil =>
      (* A dummy value serves as the tail. *)
      MLam (MVar 0)
  | t :: ts =>
      MPair t (MTuple ts)
  end.

Fixpoint MProj i t :=
  match i with
  | 0 =>
      (* Take the left pair component. *)
      MPi 0 t
  | S i =>
      (* Take the right pair component and continue. *)
      MProj i (MPi 1 t)
  end.

Definition MLetPair t u :=
  MLet (* x_0 = *) (MPi 0 t) (
    MLet (* x_1 = *) (MPi 1 (lift 1 t))
      u
  ).

(* -------------------------------------------------------------------------- *)

(* [MMultiLet 0 ts u] is a sequence of [MLet] bindings. [n] variables, where
   [n] is [length ts], are bound to the terms [ts] in the term [u]. The
   recursive structure of the definition is such that the *last* term in the
   list [ts] is bound *last*, hence is referred to as variable 0 in [u]. *)

Fixpoint MMultiLet i ts u :=
  match ts with
  | nil =>
      u
  | t :: ts =>
      MLet (lift i t) (MMultiLet (i + 1) ts u)
  end.

(* The auxiliary parameter [i] in [MMultiLet i ts u] is required for the
   recursive definition to go through, but, as far as the end user is
   concerned, is not very useful. It can be eliminated as follows. *)

Lemma MMultiLet_ij:
  forall ts delta i j u,
  i + delta = j ->
  MMultiLet j ts u = MMultiLet i (map (fun t => lift delta t) ts) u.
Proof.
  induction ts; intros; simpl; eauto.
  f_equal.
  { asimpl. congruence. }
  { erewrite IHts. eauto. omega. }
Qed.

Lemma MMultiLet_i0:
  forall i ts u,
  MMultiLet i ts u = MMultiLet 0 (map (fun t => lift i t) ts) u.
Proof.
  eauto using MMultiLet_ij with omega.
Qed.

(* -------------------------------------------------------------------------- *)

(* [MVars n] is the list [MVar 0, ..., MVar (n-1)]. *)

Definition MVars (n : nat) : list metal :=
  map MVar (nats n).

(* -------------------------------------------------------------------------- *)

(* [MProjs n t] is the list [MProj n t, ..., MProj 1 t]. *)

Definition MProjs (n : nat) (t : metal) :=
  map (fun i => MProj (i + 1) t) (rev_nats n).

(* This list has length [n]. *)

Lemma length_MProjs:
  forall n t,
  length (MProjs n t) = n.
Proof.
  unfold MProjs. intros. rewrite map_length, length_rev_nats. eauto.
Qed.

Hint Rewrite length_MProjs : length.

(* -------------------------------------------------------------------------- *)

(* Substitution (boilerplate lemmas). *)

Lemma subst_MVar:
  forall x sigma,
  (MVar x).[sigma] = sigma x.
Proof.
  intros. autosubst.
Qed.

Lemma subst_MLam:
  forall t sigma,
  (MLam t).[sigma] = MLam t.[up sigma].
Proof.
  intros. autosubst.
Qed.

Lemma subst_MApp:
  forall t1 t2 sigma,
  (MApp t1 t2).[sigma] = MApp t1.[sigma] t2.[sigma].
Proof.
  intros. autosubst.
Qed.

Lemma subst_MLet:
  forall t1 t2 sigma,
  (MLet t1 t2).[sigma] = MLet t1.[sigma] t2.[up sigma].
Proof.
  intros. autosubst.
Qed.

Lemma subst_MPair:
  forall t1 t2 sigma,
  (MPair t1 t2).[sigma] = MPair t1.[sigma] t2.[sigma].
Proof.
  intros. autosubst.
Qed.

Lemma subst_MPi:
  forall i t sigma,
  (MPi i t).[sigma] = MPi i t.[sigma].
Proof.
  intros. autosubst.
Qed.

Lemma subst_MTuple:
  forall ts sigma,
  (MTuple ts).[sigma] = MTuple (map (subst sigma) ts).
Proof.
  induction ts; intros; asimpl; [ | rewrite IHts ]; reflexivity.
Qed.

Lemma subst_MProj:
  forall n t sigma,
  (MProj n t).[sigma] = MProj n t.[sigma].
Proof.
  induction n; intros; asimpl; [ | rewrite IHn ]; autosubst.
Qed.

Lemma subst_MLetPair:
  forall t u sigma,
  (MLetPair t u).[sigma] = MLetPair t.[sigma] u.[upn 2 sigma].
Proof.
  unfold MLetPair. intros. autosubst.
Qed.

Lemma subst_MMultiLet:
  forall ts i u sigma,
  (MMultiLet i ts u).[upn i sigma] =
  MMultiLet i (map (subst sigma) ts) u.[upn (length ts) (upn i sigma)].
Proof.
  induction ts; intros; asimpl; f_equal.
  { erewrite plus_upn by tc. eauto. }
  { rewrite IHts.
    repeat erewrite upn_upn by tc.
    do 3 f_equal. omega. }
Qed.

Lemma subst_MMultiLet_0:
  forall ts u sigma,
  (MMultiLet 0 ts u).[sigma] =
  MMultiLet 0 (map (subst sigma) ts) u.[upn (length ts) sigma].
Proof.
  intros.
  change sigma with (upn 0 sigma) at 1.
  eapply subst_MMultiLet.
Qed.

Lemma subst_MVars:
  forall n sigma,
  map (subst sigma) (MVars n) = map sigma (nats n).
Proof.
  intros. unfold MVars. rewrite map_map. reflexivity.
Qed.

Lemma subst_MProjs:
  forall n t sigma,
  map (subst sigma) (MProjs n t) = MProjs n t.[sigma].
Proof.
  unfold MProjs. induction n; intros; simpl; eauto.
  rewrite subst_MProj, IHn. eauto.
Qed.

Hint Rewrite
  subst_MVar subst_MLam subst_MApp subst_MLet subst_MPair subst_MPi
  subst_MTuple subst_MProj subst_MLetPair
  subst_MMultiLet subst_MMultiLet_0
  subst_MVars subst_MProjs
: subst.

(* -------------------------------------------------------------------------- *)

(* Free variables (boilerplate lemmas). *)

Lemma fv_MVar:
  forall x k,
  fv k (MVar x) <-> x < k.
Proof.
  eauto using fv_ids_eq.
Qed.

Ltac prove_fv :=
  unfold fv; intros; asimpl;
  split; intros; unpack; [ injections | f_equal ]; eauto.

Lemma fv_MLam:
  forall t k,
  fv k (MLam t) <-> fv (k + 1) t.
Proof.
  prove_fv.
Qed.

Lemma fv_MApp:
  forall t1 t2 k,
  fv k (MApp t1 t2) <-> fv k t1 /\ fv k t2.
Proof.
  prove_fv.
Qed.

Lemma fv_MLet:
  forall t1 t2 k,
  fv k (MLet t1 t2) <-> fv k t1 /\ fv (k + 1) t2.
Proof.
  prove_fv.
Qed.

Lemma fv_MPair:
  forall t1 t2 k,
  fv k (MPair t1 t2) <-> fv k t1 /\ fv k t2.
Proof.
  prove_fv.
Qed.

Lemma fv_MPi:
  forall i t k,
  fv k (MPi i t) <-> fv k t.
Proof.
  prove_fv.
Qed.

Hint Rewrite fv_MVar fv_MLam fv_MApp fv_MLet fv_MPair fv_MPi : fv.

Lemma fv_MTuple:
  forall k ts,
  fv k (MTuple ts) <-> Forall (fv k) ts.
Proof.
  induction ts; simpl; intros; fv; split; intros; unpack.
  { econstructor. }
  { omega. }
  { rewrite IHts in *. econstructor; eauto. }
  { rewrite IHts in *. pick Forall invert. eauto. }
Qed.

Lemma fv_MProj:
  forall k n t,
  fv k (MProj n t) <-> fv k t.
Proof.
  induction n; intros; simpl; [ | rewrite IHn ]; fv; tauto.
Qed.

Lemma fv_MLetPair:
  forall k t u,
  fv k (MLetPair t u) <-> fv k t /\ fv (k + 2) u.
Proof.
  intros. unfold MLetPair. fv; tc.
  replace (k + 1 + 1) with (k + 2) by omega.
  tauto.
Qed.

Local Lemma MLet_inj:
  forall t1 u1 t2 u2,
  MLet t1 u1 = MLet t2 u2 <-> t1 = t2 /\ u1 = u2.
Proof.
  split; intros; injections; unpack; subst; eauto.
Qed.

Local Lemma cons_cons_eq:
  forall {A} (x1 x2 : A) xs1 xs2,
  x1 :: xs1 = x2 :: xs2 <->
  x1 = x2 /\ xs1 = xs2.
Proof.
  split; intros; injections; unpack; subst; eauto.
Qed.

Local Lemma MMultiLet_inj:
  forall ts1 u1 ts2 u2 i,
  length ts1 = length ts2 ->
  MMultiLet i ts1 u1 = MMultiLet i ts2 u2 <->
  ts1 = ts2 /\ u1 = u2.
Proof.
  induction ts1; destruct ts2; intros; simpl;
  try solve [ false; simpl in *; omega ].
  { tauto. }
  { rewrite MLet_inj.
    rewrite lift_injn_eq.
    rewrite IHts1 by (simpl in *; omega).
    rewrite cons_cons_eq.
    tauto. }
Qed.

Local Lemma map_inj:
  forall {A} (f : A -> A) xs,
  map f xs = xs <->
  Forall (fun x => f x = x) xs.
Proof.
  induction xs; simpl; intros; split; intros; eauto using Forall;
  injections.
  { econstructor; tauto. }
  { pick Forall invert. f_equal; tauto. }
Qed.

Lemma fv_MMultiLet_0:
  forall ts u k,
  fv k (MMultiLet 0 ts u) <->
  Forall (fv k) ts /\ fv (k + length ts) u.
Proof.
  intros. unfold fv.
  autorewrite with subst.
  rewrite MMultiLet_inj by eauto using map_length.
  rewrite upn_upn, Nat.add_comm.
  rewrite map_inj.
  tauto.
Qed.

Lemma fv_MVars:
  forall n,
  Forall (fv n) (MVars n) <->
  True.
Proof.
  split; [ eauto | intros _ ].
  unfold MVars, nats.
  eapply Forall_map.
  eapply Forall_seq; intros.
  fv. omega.
Qed.

Lemma fv_MProjs:
  forall k n t,
  fv k t -> (* not an equivalence, as [k] could be zero *)
  Forall (fv k) (MProjs n t).
Proof.
  unfold MProjs. induction n; simpl; intros;
  econstructor; [ rewrite fv_MProj |]; eauto.
Qed.

Hint Rewrite
  fv_MTuple fv_MProj fv_MLetPair fv_MMultiLet_0
  fv_MVars
  (* not fv_MProjs *)
: fv.

(* -------------------------------------------------------------------------- *)

(* The following lemma is analogous to [fv_unaffected_regular], except it does
   not have a regularity hypothesis, which makes it more pleasant to use. It is
   proved by induction on terms, which is why we are unable to prove it in a
   generic setting. *)

Lemma fv_unaffected:
  forall t k sigma,
  fv k t ->
  t.[upn k sigma] = t.
Proof.
  induction t; intros; fv; unpack; asimpl; repeat rewrite Nat.add_1_r in *;
  try solve [ eauto using upn_k_sigma_x with typeclass_instances
            | f_equal; eauto ].
Qed.

(* A corollary. *)

Lemma closed_unaffected:
  forall t sigma,
  closed t ->
  t.[sigma] = t.
Proof.
  unfold closed. intros.
  rewrite <- (upn0 sigma).
  eauto using fv_unaffected.
Qed.
