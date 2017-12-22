Require Import MyTactics.
Require Import Sequences.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusFreeVars.
Require Import LambdaCalculusReduction.

(* This file defines an encoding of call-by-name into call-by-value. This is a
   simple encoding, based on two combinators [delay] and [force]. [delay] is
   implemented as a function which ignores its argument, and [force] as a
   function call with a dummy actual argument. The proof of semantic
   preservation involves parallel call-by-value reduction. *)

(* -------------------------------------------------------------------------- *)

(* To delay the evaluation of [t], we wrap it in a function which ignores its
   argument. *)

Definition delay t :=
  Lam (lift 1 t).

(* To force the evaluation of a thunk (a delayed computation), we apply it to
   a dummy actual argument. *)

Definition dummy :=
  Lam (Var 0).

Definition force t :=
  App t dummy.

(* The key property that is expected of [force] and [delay] is of course that
   [force (delay t)] reduces to [t] under call-by-value reduction. *)

Lemma force_delay:
  forall t,
  cbv (force (delay t)) t.
Proof.
  intros. unfold force, delay. econstructor; obvious. autosubst.
Qed.

(* Obviously, [delay] and [force] commute with substitutions. *)

Lemma delay_subst:
  forall t sigma,
  (delay t).[sigma] = delay t.[sigma].
Proof.
  unfold delay. intros. autosubst.
Qed.

Lemma force_subst:
  forall t sigma,
  (force t).[sigma] = force t.[sigma].
Proof.
  unfold force. intros. autosubst.
Qed.

(* Finally, although ordinary reduction under [delay is not permitted,
   parallel reduction under [delay] is permitted. *)

Lemma pcbv_delay:
  forall t1 t2,
  pcbv t1 t2 ->
  pcbv (delay t1) (delay t2).
Proof.
  unfold delay. intros. econstructor; eauto using red_subst with obvious.
Qed.

Local Hint Resolve pcbv_delay : obvious.

(* That is all we need to know about [force] and [delay]. We now make them
   opaque, so as to prevent their unfolding during the proofs that follow. *)

Opaque force delay.

(* -------------------------------------------------------------------------- *)

(* This is the encoding of call-by-name into call-by-value. It is simple:
   in short, in every application, the actual argument is wrapped in a
   [delay]; accordingly, every use of a variable involves a [force]. *)

Fixpoint encode (t : term) :=
  match t with
  | Var x =>
      force (Var x)
  | Lam t =>
      Lam (encode t)
  | App t1 t2 =>
      App (encode t1) (delay (encode t2))
  | Let t1 t2 =>
      Let (delay (encode t1)) (encode t2)
  end.

(* -------------------------------------------------------------------------- *)

(* A naive attempt at a simulation diagram, which (if it were true) would
   imply semantic preservation. *)

Lemma encode_simulation:
  forall t1 t2,
  cbn t1 t2 ->
  cbv (encode t1) (encode t2).
Proof.
  induction 1; intros; subst; simpl; try solve [ tauto ].
  (* Beta *)
  { econstructor; eauto.
    (* This fails because [encode] does not quite commute with
       substitution. The intuition is, it almost commutes, but
       this introduces [force/delay] pairs. *)
Abort.

(* -------------------------------------------------------------------------- *)

(* [encode] commutes with renamings. *)

Lemma encode_renaming:
  forall t sigma,
  is_ren sigma ->
  (encode t).[sigma] = encode t.[sigma].
Proof.
  induction t; intros; asimpl;
  repeat rewrite delay_subst;
  repeat f_equal; obvious.
  (* Var *)
  { pick is_ren invert. reflexivity. }
Qed.

Lemma encode_lift:
  forall t k,
  lift k (encode t) = encode (lift k t).
Proof.
  eauto using encode_renaming with obvious.
Qed.

(* -------------------------------------------------------------------------- *)

(* In order to express the fact that [encode] commutes with substitutions, we
   define the following relation between substitutions. *)

(* [sigma1] is a target-level substitution, intended to be applied after
   [encode], whereas [sigma2] is a source-level substitution, intended to be
   applied before [encode]. *)

(* Because [sigma1] typically maps variables to terms that have a [delay] at
   the root, we allow [force (sigma1 x)] to reduce to [encode (sigma2 x)].
   We use parallel reduction [pcbv], even though we could perhaps use a
   slightly more precise relation at this point (such as "at most one step
   of [cbv]") because it is convenient and [pcbv] must be used in the
   conclusion of the lemma [encode_subst] anyway. *)

Local Definition related (sigma1 sigma2 : var -> term) :=
  forall x, pcbv (force (sigma1 x)) (encode (sigma2 x)).

(* This relation is preserved by [up]. *)

Local Lemma up_related:
  forall sigma1 sigma2,
  related sigma1 sigma2 ->
  related (up sigma1) (up sigma2).
Proof.
  unfold related. intros. destruct x as [|x]; asimpl.
  (* Variable 0. This case goes through because [pcbv] is reflexive. *)
  { eapply red_refl; obvious. }
  (* Variables above 0. This case goes through because [force], [encode]
     and [pcbv] are compatible with [lift 1]. *)
  { rewrite <- force_subst.
    rewrite <- encode_lift.
    eapply red_subst; obvious. }
Qed.

Local Hint Resolve up_related : obvious.

(* [encode] commutes with substitutions in the following sense. *)

Local Lemma encode_subst:
  forall t sigma1 sigma2,
  related sigma1 sigma2 ->
  pcbv
    (encode t).[sigma1]
    (encode t.[sigma2]).
Proof.
  induction t; simpl; intros; subst;
  repeat rewrite force_subst;
  repeat rewrite delay_subst;
  eauto 6 with obvious.
Qed.

(* We obtain the following corollary for singleton substitutions. *)

Local Lemma encode_subst_singleton:
  forall t1 t2,
  pcbv
    (encode t1).[delay (encode t2)/]
    (encode t1.[t2/]).
Proof.
  intros.
  eapply encode_subst.
  intros [|x]; asimpl.
  (* Variable 0. This case goes through by [force_delay]. *)
  { eauto using cbv_subset_pcbv, force_delay. }
  (* Variables above 0. This case goes through because [pcbv] is reflexive. *)
  { eapply red_refl; obvious. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Equipped with the previous substitution lemma, it is straightforward to
   establish the following simulation diagram: if [t1] steps to [t2] under
   call-by-name reduction, then [encode t1] steps to [encode t2] in at
   least one step of parallel call-by-value reduction. *)

Lemma encode_simulation:
  forall t1 t2,
  cbn t1 t2 ->
  plus pcbv (encode t1) (encode t2).
Proof.
  induction 1; simpl; intros; subst; try solve [ tauto ].
  (* Beta. Two steps of reduction are required. *)
  { econstructor. { eauto using cbv_subset_pcbv with obvious. }
    econstructor. { eauto using encode_subst_singleton. }
    finished. eauto. }
  (* Let. Two steps of reduction are required. *)
  { econstructor. { eauto using cbv_subset_pcbv with obvious. }
    econstructor. { eauto using encode_subst_singleton. }
    finished. eauto. }
  (* AppL. Just perform reduction under a context. *)
  { obvious. }
Qed.
