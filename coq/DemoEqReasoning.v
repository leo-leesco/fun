Require Import List.

Section Demo.

(* -------------------------------------------------------------------------- *)

Variables A B : Type.
Variable  p   : B -> bool.
Variable  f   : A -> B.

(* The composition of [filter] and [map] can be computed by the specialized
   function [filter_map]. *)

Fixpoint filter_map xs :=
  match xs with
  | nil =>
      nil
  | cons x xs =>
      let y := f x in
      if p y then y :: filter_map xs else filter_map xs
  end.

Lemma filter_map_spec:
  forall xs,
  filter p (map f xs) = filter_map xs.
Proof.
  induction xs as [| x xs ]; simpl.
  { reflexivity. }
  { rewrite IHxs. reflexivity. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [filter] and [map] commute in a certain sense. *)

Variable q : A -> bool.

Lemma filter_map_commute:
  (forall x, p (f x) = q x) ->
  forall xs,
  filter p (map f xs) = map f (filter q xs).
Proof.
  intros h.
  induction xs as [| x xs ]; simpl; intros.
  (* Case: [nil]. *)
  { reflexivity. }
  (* Case: [x :: xs]. *)
  { rewrite h.
    rewrite IHxs.
    (* Case analysis: [q x] is either true or false.
       In either case, the result is immediate. *)
    destruct (q x); reflexivity. }
Qed.

(* In a slightly stronger version of the lemma, the equality [p (f x) = q x]
   needs to be proved only under the hypothesis that [x] is an element of the
   list [xs]. *)

Lemma filter_map_commute_stronger:
  forall xs,
  (forall x, In x xs -> p (f x) = q x) ->
  filter p (map f xs) = map f (filter q xs).
Proof.
  induction xs as [| x xs ]; simpl; intro h.
  { reflexivity. }
  { (* The proof is the same as above, except the two rewriting steps have
       side conditions, which are immediately proved by [eauto]. *)
    rewrite h by eauto.
    rewrite IHxs by eauto.
    destruct (q x); reflexivity. }
Qed.

End Demo.
