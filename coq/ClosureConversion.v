Require Import List.
Require Import MyList.
Require Import MyTactics.
Require Import Sequences.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusFreeVars.
Require Import LambdaCalculusValues.
Require Import LambdaCalculusBigStep.
Require Import MetalSyntax.
Require Import MetalBigStep.

(* This file contains a definition of closure conversion and a proof of
   semantic preservation. Closure conversion is a transformation of the
   lambda-calculus into a lower-level calculus, nicknamed Metal, where
   lambda-abstractions must be closed. *)

(* The definition is slightly painful because we are using de Bruijn indices.
   (That said, it is likely that using named variables would be painful too,
   just in other ways.) One important pattern that we follow is that, as soon
   as a variable [x] is no longer useful, we use [eos x _] to make it go out
   of scope. Following this pattern is not just convenient -- it is actually
   necessary. *)

(* The main transformation function, [cc], has type [nat -> term -> metal]. If
   [t] is a source term with [n] free variables, then [cc n t] is its image
   under the transformation. *)

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* The auxiliary function [cc_lam n cct] defines the transformation of
   the body of a lambda-abstraction. This auxiliary function must be isolated
   because it is used twice, once within [cc], and once within [cc_value]. *)

(* The parameter [n] is supposed to be the number of free variables of the
   lambda-abstraction, and the parameter [cct] is the body of the transformed
   lambda-abstraction. That is, [cct] is expected to be later instantiated
   with [cc (n + 1) t], where [t] is the body of the source
   lambda-abstraction. *)

(* The term [cc_lam n cct] has just one free variable, namely 0, which
   represents the formal parameter of the transformed lambda-abstraction. This
   parameter is expected to be a pair [(clo, x)], where [clo] is the closure
   and [x] is the formal parameter of the source lambda-abstraction. *)

(* In nominal / informal syntax, the code would be roughly:

     let (clo, x) = _ in
     let x_1, ..., x_n = pi_1 clo, ..., pi_n clo in
     cct

*)

(* We use meta-level [let] bindings, such as [let clo_x := 0 in ...].
   These bindings generate no Metal code -- they should not be confused
   with Metal [MLet] bindings. They are just a notational convenience. *)

Definition cc_lam (n : nat) (cct : metal) : metal :=
  (* Let us refer to variable 0 as [clo_x]. *)
  let clo_x := 0 in
  (* Initially, the variable [clo_x] is bound to a pair of [clo] and [x].
     Decompose this pair, then let [clo_x] go out of scope. *)
  MLetPair (* clo, x *) (MVar clo_x) (
  let clo_x := clo_x + 2 in
  eos clo_x (
  (* Two variables are now in scope, namely [clo] and [x]. *)
  let clo := 1 in
  let x := 0 in
  (* Now, bind [n] variables, informally referred to as [x_1, ..., x_n],
     to the [n] tuple projections [pi_1 clo, ..., pi_n clo]. Then, let
     [clo] go out of scope, as it is no longer needed. *)
  MMultiLet 0 (MProjs n (MVar clo)) (
  let clo := n + clo in
  let x := n + x in
  eos clo (
  (* We need [x] to correspond to de Bruijn index 0. Currently, this is
     not the case. So, rebind a new variable to [x], and let the old [x]
     go out of scope. (Yes, this is a bit subtle.) We use an explicit
     [MLet] binding, but in principle, could also use a substitution. *)
  MLet (MVar x) (
  let x := 1 + x in
  eos x (
  (* We are finally ready to enter the transformed function body. *)
  cct
  )))))).

(* [cc] is the main transformation function. *)

Fixpoint cc (n : nat) (t : term) : metal :=
  match t with

  | Var x =>
      (* A variable is mapped to a variable. *)
      MVar x

  | Lam t =>
      (* A lambda-abstraction [Lam t] is mapped to a closure, that is, a tuple
         whose 0-th component is a piece of code (a closed lambda-abstraction)
         and whose remaining [n] components are the [n] variables numbered 0,
         1, ..., n-1. *)
      MTuple (
        MLam (cc_lam n (cc (n + 1) t)) ::
        MVars n
      )

  | App t1 t2 =>
      (* A function application is transformed into a closure invocation. *)
      (* Bind [clo] to the closure produced by the (transformed) term [t1]. *)
      MLet (cc n t1) (
      let clo := 0 in
      (* Bind [code] to the 0-th component of this closure. *)
      MLet (MProj 0 (MVar clo)) (
      let clo := 1 + clo in
      let code := 0 in
      (* Apply the function [code] to a pair of the closure and the value
         produced by the (transformed) term [t2]. Note that both [clo] and
         [code] must go out of scope before referring to [t2]. This could
         be done in one step by applying the renaming [(+2)], but we prefer
         to explicitly use [eos] twice, for greater clarity. *)
      MApp
        (MVar code)
        (MPair
           (MVar clo)
           (eos clo (eos code (cc n t2)))
        )
      ))

  | Let t1 t2 =>
      (* A local definition is translated to a local definition. *)
      MLet (cc n t1) (cc (n + 1) t2)

  end.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* In order to prove that the above program transformation is sound (that is,
   semantics-preserving), we must relate the values computed by the source
   program with the values computed by the target program. Fortunately, the
   relation is simple. (It is, in fact, a function.) The image of a source
   closure [Clo t e] under the translation is a closure, represented as a
   tuple, whose 0-th component is a lambda-abstraction -- the translation
   of [Lam t] -- and whose remaining [n] components are the translation of
   the environment [e]. *)

Fixpoint cc_cvalue (cv : cvalue) : mvalue :=
  match cv with
  | Clo t e =>
      let n := length e in
      MVTuple (
        MVLam (cc_lam n (cc (n + 1) t)) ::
        map cc_cvalue e
      )
  end.

(* The translation of environments is defined pointwise. *)

Definition cc_cenv e :=
  map cc_cvalue e.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* This lemma and hint increase the power of the tactic [length]. *)

Lemma length_cc_env:
  forall e,
  length (cc_cenv e) = length e.
Proof.
  intros. unfold cc_cenv. length.
Qed.

Hint Rewrite length_cc_env : length.

(* In this file, we allow [eauto with omega] to use the tactic [length]. *)

Local Hint Extern 1 (_ = _ :> nat) => length : omega.
Local Hint Extern 1 (lt _ _) => length : omega.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* We now check two purely syntactic properties of the transformation. First,
   if the source program [t] has [n] free variables, then the transformed
   program [cc n t] has [n] free variables, too. Second, in the transformed
   program, every lambda-abstraction is closed. *)

(* These proofs are "easy" and "routine", but could have been fairly lengthy
   and painful if we had not set up appropriate lemmas and tactics, such as
   [fv], beforehand. *)

Lemma fv_cc_lam:
  forall m n t,
  fv (S n) t ->
  1 <= m ->
  fv m (cc_lam n t).
Proof.
  intros. unfold cc_lam. fv; length. repeat split;
  eauto using fv_monotonic with omega.
  { eapply fv_MProjs. fv. omega. }
Qed.

Lemma fv_cc:
  forall t n1 n2,
  fv n2 t ->
  n1 = n2 ->
  fv n1 (cc n2 t).
Proof.
  induction t; intros; subst; simpl; fv; unpack;
  repeat rewrite Nat.add_1_r in *;
  repeat split; eauto using fv_monotonic, fv_cc_lam with omega.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas help reorganize our view of the environment. They are
   typically used just before applying the lemma [mbigcbv_eos], that is, when
   a variable [x] is about to go out of scope. We then want to organize the
   environment so that it has the shape [e1 ++ mv :: e2], where the length of
   [e1] is [x], so [mv] is the value that is dropped, and the environment
   afterwards is [e1 ++ e2]. *)

Local Lemma access_1:
  forall {A} xs (x0 x : A),
  x0 :: x :: xs = (x0 :: nil) ++ x :: xs.
Proof.
  reflexivity.
Qed.

Local Lemma access_2:
  forall {A} xs (x0 x1 x : A),
  x0 :: x1 :: x :: xs = (x0 :: x1 :: nil) ++ x :: xs.
Proof.
  reflexivity.
Qed.

Local Lemma access_n_plus_1:
  forall {A} xs (x : A) ys,
  xs ++ x :: ys = (xs ++ x :: nil) ++ ys.
Proof.
  intros. rewrite <- app_assoc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* We now establish a (forward) semantic preservation statement: if under
   environment [e] the source term [t] computes the value [cv], then under
   the translation of [e], the translation of [t] computes the translation
   of [cv]. *)

(* The proof is fairly routine and uninteresting; it is just a matter of
   checking that everything works as expected. A crucial point that helps
   keep the proof manageable is that we have defined auxiliary evaluation
   lemmas for tuples, projections, [MMultiLet], and so on. *)

(* Although the proof is not "hard", it would be difficult to do by hand, as
   it is quite deep and one must keep track of many details, such as the shape
   of the runtime environment at every program point -- that is, which de
   Bruijn index is bound to which value. An off-by-one error in a de Bruijn
   index, or a list that is mistakenly reversed, would be difficult to detect
   in a handwritten proof. Machine assistance is valuable in this kind of
   exercise. *)

Theorem semantic_preservation:
  forall e t cv,
  ebigcbv e t cv ->
  forall n,
  n = length e ->
  mbigcbv (cc_cenv e) (cc n t) (cc_cvalue cv).
Proof.
  induction 1; intros; simpl.

  (* Case: [Var]. Nothing much to say; apply the evaluation rule and
     check that its side conditions hold. *)
  { econstructor.
    { length. }
    { subst cv.
      erewrite (nth_indep (cc_cenv e)) by length.
      unfold cc_cenv. rewrite map_nth. eauto. }
  }

  (* Case: [Lam]. We have to check that a transformed lambda-abstraction
     (as per [cc]) evaluates to a transformed closure (as per [cc_value]).
     This is fairly easy. *)
  { subst. econstructor.
    (* The code component. We must check that it is closed. *)
    { econstructor.
      assert (fv (length e + 1) t).
      { eapply (use_fv_length_cons _ dummy_cvalue); eauto. }
      unfold closed. fv. eauto using fv_cc_lam, fv_cc with omega. }
    (* The remaining components. *)
    { eapply MBigcbvTuple.
      rewrite <- length_cc_env. eauto using MBigcbvVars. }
  }

  (* Case: [App]. This is where most of the action takes place. We must
     essentially "execute" the calling sequence and check that it works
     as expected. *)

  { (* Evaluate the first [Let], which binds a variable [clo] to the closure. *)
    econstructor. { eauto. }
    (* Evaluate the second [Let], which projects the code out of the closure,
       and binds the variable [code]. *)
    econstructor.
    { econstructor; [| eauto ].
      econstructor; simpl; eauto with omega. }
    (* We are now looking at a function application. Evaluate in turn the function,
       its actual argument, and the call itself. *)
    econstructor.
    (* The function. *)
    { econstructor; simpl; eauto with omega. }
    (* Its argument. *)
    { econstructor.
      { econstructor; simpl; eauto with omega. }
      { (* Skip two [eos] constructs. *)
        rewrite access_1. eapply mbigcbv_eos; [ simpl | length ].
        eapply mbigcbv_eos with (e1 := nil); [ simpl | length ].
        eauto. }
    }
    (* The call itself. Here, we step into a transformed lambda-abstraction, and
       we begin studying how it behaves when executed. *)
    unfold cc_lam at 2.
    (* Evaluate [MLetPair], which binds [clo] and [x]. *)
    eapply MBigcbvLetPair.
    { econstructor; simpl; eauto with omega. }
    (* Skip [eos]. *)
    rewrite access_2. eapply mbigcbv_eos; [ simpl | eauto ].
    (* Evaluate [MMultiLet]. *)
    eapply MBigcbvMultiLetProjs.
    { econstructor; simpl; eauto with omega. }
    { length. }
    (* Skip [eos]. *)
    rewrite access_n_plus_1. eapply mbigcbv_eos; [| length ].
    rewrite app_nil_r, Nat.add_0_r.
    (* Evaluate the new binding of [x]. *)
    econstructor.
    { econstructor.
      { length. }
      { rewrite app_nth by (rewrite map_length; omega). simpl. eauto. }
    }
    (* Skip [eos]. *)
    rewrite app_comm_cons. eapply mbigcbv_eos; [ rewrite app_nil_r | length ].
    (* Evaluate the function body. *)
    eauto with omega. }

  (* Case: [Let]. Immediate. *)
  { econstructor; eauto with omega. }

Qed.
