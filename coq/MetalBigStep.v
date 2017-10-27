Require Import List.
Require Import MyList.
Require Import MyTactics.
Require Import Sequences.
Require Import MetalSyntax.
Require Import Autosubst_Env.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* A big-step call-by-value semantics with explicit environments. *)

(* Because every lambda-abstraction is closed, no closures are involved:
   a lambda-abstraction evaluates to itself. Thus, an mvalue [mv] must be
   either a (closed) lambda-abstraction or a pair of mvalues. *)

Inductive mvalue :=
| MVLam  : {bind metal} -> mvalue
| MVPair : mvalue -> mvalue -> mvalue.

Definition dummy_mvalue : mvalue :=
  MVLam (MVar 0).

(* An environment [e] is a list of mvalues. *)

Definition menv :=
  list mvalue.

(* The judgement [mbigcbv e t mv] means that, under the environment [e], the
   term [t] evaluates to [mv]. *)

Inductive mbigcbv : menv -> metal -> mvalue -> Prop :=
| MBigcbvVar:
    forall e x mv,
    (* The variable [x] must be in the domain of [e]. *)
    x < length e ->
    (* This allows us to safely look up [e] at [x]. *)
    mv = nth x e dummy_mvalue ->
    mbigcbv e (MVar x) mv
| MBigcbvLam:
    forall e t,
    (* The lambda-abstraction must have no free variables. *)
    closed (MLam t) ->
    mbigcbv e (MLam t) (MVLam t)
| MBigcbvApp:
    forall e t1 t2 u1 mv2 mv,
    (* Evaluate [t1] to a lambda-abstraction, *)
    mbigcbv e t1 (MVLam u1) ->
    (* evaluate [t2] to a value, *)
    mbigcbv e t2 mv2 ->
    (* and evaluate the function body in a singleton environment. *)
    mbigcbv (mv2 :: nil) u1 mv ->
    mbigcbv e (MApp t1 t2) mv
| MBigcbvLet:
    forall e t1 t2 mv1 mv,
    (* Evaluate [t1] to a value, *)
    mbigcbv e t1 mv1 ->
    (* and evaluate [t2] under a suitable environment. *)
    mbigcbv (mv1 :: e) t2 mv ->
    mbigcbv e (MLet t1 t2) mv
| MBigcbvPair:
    forall e t1 t2 mv1 mv2,
    (* Evaluate each component to a value, *)
    mbigcbv e t1 mv1 ->
    mbigcbv e t2 mv2 ->
    (* and construct a pair. *)
    mbigcbv e (MPair t1 t2) (MVPair mv1 mv2)
| MBigcbvPi:
    forall e i t mv1 mv2 mv,
    (* Evaluate [t] to a pair value, *)
    mbigcbv e t (MVPair mv1 mv2) ->
    (* and project out the desired component. *)
    mv = match i with 0 => mv1 | _ => mv2 end ->
    mbigcbv e (MPi i t) mv
.

Hint Constructors mbigcbv : mbigcbv.

(* -------------------------------------------------------------------------- *)

(* A reformulation of the evaluation rule for variables. *)

Lemma MBigcbvVarExact:
  forall e1 mv e2 x,
  x = length e1 ->
  mbigcbv (e1 ++ mv :: e2) (MVar x) mv.
Proof.
  intros. econstructor.
  { length. }
  { rewrite app_nth by eauto. reflexivity. }
Qed.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* We now examine how the big-step semantics interacts with renamings.
   We prove that if (roughly) the equation [e = xi >>> e'] holds then
   evaluating [t.[xi]] under [e'] is the same as evaluating [t] under
   [e]. *)

Lemma mbigcbv_ren:
  forall e t mv,
  mbigcbv e t mv ->
  forall e' xi,
  env_ren_comp e xi e' ->
  mbigcbv e' t.[ren xi] mv.
Proof.
  induction 1; intros;
  try solve [ asimpl; eauto with env_ren_comp mbigcbv ].
  (* MVar *)
  { pick @env_ren_comp invert.
    econstructor; eauto. }
  (* MLam *)
  { rewrite closed_unaffected by eauto.
    eauto with mbigcbv. }
Qed.

(* As a special case, evaluating [eos x t] under an environment of the form
   [e1 ++ mv :: e2], where length of [e1] is [x] (so [x] is mapped to [mv])
   is the same as evaluating [t] under [e1 ++ e2]. The operational effect
   of the end-of-scope mark [eos x _] is to delete the value stored at index
   [x] in the evaluation environment. *)

Lemma mbigcbv_eos:
  forall e1 e2 x t mv mw,
  mbigcbv (e1 ++ e2) t mw ->
  x = length e1 ->
  mbigcbv (e1 ++ mv :: e2) (eos x t) mw.
Proof.
  intros. eapply mbigcbv_ren; eauto with env_ren_comp.
Qed.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* Evaluation rules for (simulated) tuples. *)

Fixpoint MVTuple mvs :=
  match mvs with
  | nil =>
      MVLam (MVar 0)
  | mv :: mvs =>
      MVPair mv (MVTuple mvs)
  end.

Lemma MBigcbvTuple:
  forall e ts mvs,
  (* Evaluate every component to a value, *)
  Forall2 (mbigcbv e) ts mvs ->
  (* and construct a tuple. *)
  mbigcbv e (MTuple ts) (MVTuple mvs).
Proof.
  induction 1; simpl; econstructor; eauto.
  { unfold closed. fv. }
Qed.

Lemma MBigcbvProj:
  forall i e t mvs mv,
  i < length mvs ->
  (* Evaluate [t] to a tuple value, *)
  mbigcbv e t (MVTuple mvs) ->
  (* and project out the desired component. *)
  mv = nth i mvs dummy_mvalue ->
  mbigcbv e (MProj i t) mv.
Proof.
  (* By induction on [i]. In either case, [mvs] cannot be an empty list. *)
  induction i; intros; (destruct mvs as [| mv0 mvs ]; [ false; simpl in *; omega |]).
  (* Base case. *)
  { econstructor; eauto. }
  (* Step case. *)
  { assert (i < length mvs). { length. }
    simpl. eauto with mbigcbv. }
Qed.

Lemma MBigcbvLetPair:
  forall e t u mv mv1 mv2,
  mbigcbv e t (MVPair mv1 mv2) ->
  mbigcbv (mv2 :: mv1 :: e) u mv ->
  mbigcbv e (MLetPair t u) mv.
Proof.
  unfold MLetPair. eauto 6 using mbigcbv_ren, env_ren_comp_plus1 with mbigcbv.
Qed.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* Evaluation rules for [MMultiLet]. *)

Local Lemma Forall2_mbigcbv_plus1:
  forall ts mvs e i mv,
  Forall2 (mbigcbv e) (map (fun t : metal => lift i t) ts) mvs ->
  Forall2 (mbigcbv (mv :: e)) (map (fun t : metal => lift (i + 1) t) ts) mvs.
Proof.
  induction ts as [| t ts]; simpl; intros;
  pick Forall2 invert; econstructor; eauto.
  replace (lift (i + 1) t) with (lift 1 (lift i t)) by autosubst.
  eauto using mbigcbv_ren, env_ren_comp_plus1.
Qed.

Lemma MBigcbvMultiLet:
  forall ts e i u mvs mv,
  Forall2 (mbigcbv e) (map (fun t => lift i t) ts) mvs ->
  mbigcbv (rev mvs ++ e) u mv ->
  mbigcbv e (MMultiLet i ts u) mv.
Proof.
  induction ts; simpl; intros; pick Forall2 invert.
  { eauto. }
  { pick mbigcbv ltac:(fun h => rewrite rev_cons_app in h).
    econstructor; eauto using Forall2_mbigcbv_plus1. }
Qed.

Lemma MBigcbvMultiLet_0:
  forall ts e u mvs mv,
  Forall2 (mbigcbv e) ts mvs ->
  mbigcbv (rev mvs ++ e) u mv ->
  mbigcbv e (MMultiLet 0 ts u) mv.
Proof.
  intros. eapply MBigcbvMultiLet.
  { asimpl. rewrite map_id. eauto. }
  { eauto. }
Qed.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* An evaluation rule for [MVars]. *)

Lemma MBigcbvVars_preliminary:
  forall e2 e1 e x n,
  e = e1 ++ e2 ->
  x = length e1 ->
  n = length e2 ->
  Forall2 (mbigcbv e) (map MVar (seq x n)) e2.
Proof.
  induction e2 as [| mv e2 ]; intros; subst; econstructor.
  { eauto using MBigcbvVarExact. }
  { eapply IHe2 with (e1 := e1 ++ mv :: nil).
    { rewrite <- app_assoc. reflexivity. }
    { length. }
    { eauto. }
  }
Qed.

Lemma MBigcbvVars:
  forall e,
  Forall2 (mbigcbv e) (MVars (length e)) e.
Proof.
  unfold MVars, nats. intros.
  eapply MBigcbvVars_preliminary with (e1 := nil); eauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* An evaluation rule for [MProjs]. If the term [t] evaluates to a tuple whose
   components numbered 1, ..., n are collected in the list [mvs1], then the
   family of terms [MProjs n t] evaluates to the family of values [rev mvs1]. *)

Lemma MBigcbvProjs:
  forall n e t mv mvs1 mvs2,
  mbigcbv e t (MVTuple (mv :: mvs1 ++ mvs2)) ->
  length mvs1 = n ->
  Forall2 (mbigcbv e) (MProjs n t) (rev mvs1).
Proof.
  (* This result is "obvious" but requires some low-level work. *)
  unfold MProjs. induction n; intros.
  (* Case: [n] is zero. Then, [mvs1] must be [nil]. The result follows. *)
  { destruct mvs1; [| false; simpl in *; omega ].
    econstructor. }
  (* Case: [n] is nonzero. Then, the list [mvs1] must be nonempty. *)
  assert (hmvs1: mvs1 <> nil).
  { intro. subst. simpl in *. omega. }
  (* So, this list has one element at the end. Let us write this list in the
     form [mvs1 ++ mv1]. *)
  destruct (exists_last hmvs1) as (hd&mv1&?). subst mvs1. clear hmvs1.
  generalize dependent hd; intro mvs1; intros.
  (* Simplify. *)
  rewrite rev_unit.
  rewrite <- app_assoc in *.
  rewrite app_length in *.
  assert (length mvs1 = n). { length. }
  simpl map.
  econstructor.
  (* The list heads. *)
  { eapply MBigcbvProj; eauto.
    { length. }
    { replace (n + 1) with (S n) by omega. simpl.
      rewrite app_nth by omega.
      reflexivity. }
  }
  (* The list tails. *)
  { eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* An evaluation rule for the combination of [MMultiLet] and [MProjs]. If the
   term [t] evaluates to a tuple whose components are [mv :: mvs], and if [n]
   is the length of [mvs], then evaluating [MMultiLet 0 (MProjs n t) u] in an
   environment [e] leads to evaluating [u] in environment [mvs ++ e]. *)

Lemma MBigcbvMultiLetProjs:
  forall e t mvs u mv mw n,
  mbigcbv e t (MVTuple (mv :: mvs)) ->
  length mvs = n ->
  mbigcbv (mvs ++ e) u mw ->
  mbigcbv e (MMultiLet 0 (MProjs n t) u) mw.
Proof.
  intros.
  eapply MBigcbvMultiLet_0.
  { eapply MBigcbvProjs with (mvs2 := nil); [ rewrite app_nil_r |]; eauto. }
  { rewrite rev_involutive. eauto. }
Qed.
