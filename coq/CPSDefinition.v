Require Import MyTactics.
Require Import FixExtra.
Require Import LambdaCalculusSyntax.
Require Import LambdaCalculusValues.

(* This is a definition of the CPS transformation. *)

(* This CPS transformation is "one-pass" in the sense that it does not produce
   any administrative redexes. (In other words, there is no need for a second
   pass, whose purpose would be to remove administrative redexes.)

   To achieve this, instead of defining [cps t k], where the continuation [k]
   is a term, we define [cps t c], where the continuation [c] is either a term
   (also known as an object-level continuation) or a term-with-a-hole [K]
   (also known as a meta-level continuation).

   This formulation of the CPS transformation is analogous to Danvy and
   Filinski's higher-order formulation. Yet, it is still technically
   first-order, because we represent a term-with-a-hole [K] as a term,
   where the variable 0 denotes the hole. *)

(* This CPS transformation is defined by recursion on the size of terms. This
   allows recursive calls of the form [cps (lift 1 t)], which would be illegal
   if [cps] was defined by structural induction. Definitions by well-founded
   recursion in Coq are somewhat tricky, requiring the use of the fixed point
   combinator [Fix] and the tactic [refine]. For explanations, see the chapter
   on general recursion in Chlipala's book at
   http://adam.chlipala.net/cpdt/html/GeneralRec.html *)

(* The situation could be complicated by the fact that we wish to define two
   functions simultaneously:

     [cpsv v] is the translation of a value [v].

     [cps t c] is the translation of a term [t] with continuation [c].

   To avoid this problem, we follow Danvy and Filinski's approach, which is to
   first define [cps] directly (as this does not cause much duplication), then
   define [cpsv] in terms of [cps]. In the latter step, no case analysis is
   required: [cpsv] is obtained by invoking [cps] with an identity meta-level
   continuation.

   Regardless of how [cps] and [cpsv] are defined, we prove that the they
   satisfy the desired recurrence equations, so, in the end, everything is
   just as if they had been defined in a mutually recursive manner. *)

(* -------------------------------------------------------------------------- *)

(* As explained above, a continuation [c] is

     either [O k], where [k] is a term (in fact, a value)
                   (an object-level continuation)

         or [M K], where [K] is term-with-a-hole
                   (a meta-level continuation).

   A term-with-a-hole [K] is represented as a term where the variable 0 denotes
   the hole (and, of course, all other variables are shifted up). *)

Inductive continuation :=
| O (k : term)
| M (K : term).

(* The term [apply c v] is the application of the continuation [c] to the
   value [v]. If [c] is an object-level continuation [k] (that is, a term),
   then it is just the object-level application [App k v]. If [c] is a
   meta-level continuation [K], then it is the meta-level operation of filling
   the hole with the value [v], which in fact is just a substitution,
   [K.[v/]]. *)

Definition apply (c : continuation) (v : term) : term :=
  match c with
  | O k =>
      App k v
  | M K =>
      K.[v/]
  end.

(* The term [reify c] is the reification of the continuation [c] as an
   object-level continuation (that is, a term). If [c] is an object-level
   continuation [k], then it is just [k]. If [c] is a meta-level continuation
   [K], then [reify c] is the term [\x.K x]. (This is usually known as a
   two-level eta-expansion.) Because the hole is already represented by the
   variable 0, filling the hole with the variable [x] is a no-op. Therefore,
   it suffices to write [Lam K] to obtain the desired lambda-abstraction. *)

Definition reify (c : continuation) : term :=
  match c with
  | O k =>
      k
  | M K =>
      Lam K
  end.

(* The continuation [substc sigma c] is the result of applying the
   substitution [sigma] to the continuation [c]. *)

Definition substc sigma (c : continuation) : continuation :=
  match c with
  | O k =>
      O k.[sigma]
  | M K =>
      M K.[up sigma]
  end.

(* [liftc i c] is the result of lifting the free names of the continuation [c]
   up by [i]. The function [liftc] can be defined in terms of [substc]. *)

Notation liftc i c :=
  (substc (ren (+i)) c).

(* -------------------------------------------------------------------------- *)

(* Here is the definition of [cps]. Because we must keep track of sizes and
   prove that the recursive calls cause a decrease in the size, this
   definition cannot be easily written as Coq terms. Instead, we switch to
   proof mode and use the tactic [refine]. This allows us to write some of the
   code, with holes [_] in it, and use proof mode to fill the holes. *)

(* [cps t c] is the CPS-translation of the term [t] with continuation [c]. *)

Definition cps : term -> continuation -> term.
Proof.
  (* The definition is by well-founded recursion on the size of [t]. *)
  refine (Fix smaller_wf_transparent (fun _ => continuation -> term) _).
  (* We receive the arguments [t] and [c] as well as a function [cps_]
     which we use for recursive calls. At every call to [cps_], there
     is an obligation to prove that the size of the argument is less
     than the size of [t]. *)
  intros t cps_ c.
  (* The definition is by cases on the term [t]. *)
  destruct t as [ x | t | t1 t2 | t1 t2 ].
  (* When [t] is a value, we return an application of the continuation [c]
     to a value which will later be known as [cpsv t]. *)
  (* Case: [Var x]. *)
  { refine (apply c (Var x)). }
  (* Case: [Lam t]. *)
  (* In informal notation, the term [\x.t] is transformed to an application of
     [c] to [\x.\k.[cps t k]], where [k] is a fresh variable. Here, [k] is
     represented by the de Bruijn index 0, and the term [t] must be lifted
     because it is brought into the scope of [k]. *)
  { refine (apply c
      (Lam (* x *) (Lam (* k *) (cps_ (lift 1 t) _ (O (Var 0)))))
    ); abstract size. }
  (* Case: [App t1 t2]. *)
  (* The idea is, roughly, to first obtain the value [v1] of [t1], then obtain
     the value [v2] of [t2], then perform the application [v1 v2 c].

     Two successive calls to [cps] are used to obtain [v1] and [v2]. In each
     case, we avoid administrative redexes by using an [M] continuation.
     Thus, [v1] and [v2] are represented by two holes, denoted by the
     variables [Var 1] and [Var 0].

     If [t1] is a value, then the first hole will be filled directly with (the
     translation of) [t1]; otherwise, it will be filled with a fresh variable,
     bound to the result of evaluating (the translation of) [t1]. The same
     goes for [t2].

     The application [v1 v2 c] does not directly make sense, since [c] is a
     continuation, not a term. Instead of [c], we must use [reify c]. The
     continuation [c] must turned into a term, so it can be used in this
     term-level application.

     A little de Bruijn wizardry is involved. The term [t2] must be lifted up
     by 1 because it is brought into the scope of the first meta-level
     continuation. Similarly, the first hole must be lifted by 1 because it is
     brought into the scope of the second meta-level continuation: thus, it
     becomes Var 1. Finally, the continuation [c] must be lifted up by [2]
     because it is brought into the scope of both. Here, we have a choice
     between [reify (liftc _ c)] and [lift _ (reify c)], which mean the same
     thing. *)
  { refine (
      cps_ t1 _ (M (
        cps_ (lift 1 t2) _ (M (
          App (App (Var 1) (Var 0)) (lift 2 (reify c))
        ))
      ))
    );
    abstract size.
  }
  (* Case: [Let x = t1 in t2]. *)
  (* The idea is to first obtain the value [v1] of [t1]. This value is
     represented by the hole [Var 0] in the [M] continuation. We bind
     this value via a [Let] construct to the variable [x] (represented by the
     index 0 in [t2]), then execute [t2], under the original continuation [c].
     All variables in [t2] except [x] must lifted up by one because they are
     brought in the scope of the meta-level continuation. The continuation [c]
     must be lifted up by 2 because it is brought in the scope of the
     meta-level continuation and in the scope of the [Let] construct. *)
  { refine (
      cps_ t1 _ (M (
        Let (Var 0) (
          cps_ t2.[up (ren (+1))] _ (liftc 2 c)
        )
      ))
    );
    abstract size.
  }
Defined.

(* -------------------------------------------------------------------------- *)

(* The above definition can be used inside Coq to compute the image of a term
   through the transformation. For instance, the image under [cps] of [\x.x]
   with object-level continuation [k] (a variable) is [k (\x.\k.k x)]. *)

Goal
  cps (Lam (Var 0)) (O (Var 0)) =
  App (Var 0) (Lam (Lam (App (Var 0) (Var 1)))).
Proof.
  compute. (* optional *)
  reflexivity.
Qed.

(* The image of [(\x.x) y] with continuation [k] is [(\x.\k.k x) y k]. *)

Goal
  cps (App (Lam (Var 0)) (Var 0)) (O (Var 1)) =
  App (App (Lam (Lam (App (Var 0) (Var 1)))) (Var 0)) (Var 1).
Proof.
  compute. (* optional *)
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* The initial continuation is used when invoking [cps] at the top level. *)

(* We could use [O (Lam (Var 0))] -- that is, the identity function -- as
   the initial continuation. Instead, we use [M (Var 0)], that is, the
   empty context. This sometimes saves one beta-redex. *)

Definition init :=
  M (Var 0).

Definition cpsinit t :=
  cps t init.

(* -------------------------------------------------------------------------- *)

(* Now that [cps] is defined, we can define [cpsv] in terms of it. *)

(* We explicitly check whether [v] is a value, and if it is not, we return a
   dummy closed value. [cpsv] is supposed to be applied only to values,
   anyway. Using a dummy value allows us to prove that [cpsv v] is always a
   value, without requiring that [v] itself be a value. *)

Definition cpsv (v : term) :=
  if_value v
    (cpsinit v)
    (Lam (Var 0)).

(* -------------------------------------------------------------------------- *)

(* The function [cps] satisfies the expected recurrence equations. *)

(* The lemmas [cps_var] and [cps_lam] are not used outside this file, as we
   use [cps_value] instead, followed with [cpsv_var] or [cpsv_lam]. *)

Lemma cps_var:
  forall x c,
  cps (Var x) c = apply c (Var x).
Proof.
  reflexivity.
Qed.

Lemma cps_lam:
  forall t c,
  cps (Lam t) c =
    apply c (Lam (* x *) (Lam (* k *) (cps (lift 1 t) (O (Var 0))))).
Proof.
  intros. erewrite Fix_eq_simplified with (f := cps) by reflexivity.
  reflexivity.
Qed.

Lemma cps_app:
  forall t1 t2 c,
  cps (App t1 t2) c =
    cps t1 (M (
      cps (lift 1 t2) (M (
        App (App (Var 1) (Var 0)) (lift 2 (reify c))
      ))
    )).
Proof.
  intros. erewrite Fix_eq_simplified with (f := cps) by reflexivity.
  reflexivity.
Qed.

Lemma cps_let:
  forall t1 t2 c,
  cps (Let t1 t2) c =
    cps t1 (M (
      Let (Var 0) (
        cps t2.[up (ren (+1))] (liftc 2 c)
      )
    )).
Proof.
  intros. erewrite Fix_eq_simplified with (f := cps) by reflexivity.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* The translation of values is uniform: we also have the following equation. *)

Lemma cps_value:
  forall v c,
  is_value v ->
  cps v c = apply c (cpsv v).
Proof.
  destruct v; simpl; intros; try not_a_value; unfold cpsv, cpsinit.
  { rewrite !cps_var. reflexivity. }
  { rewrite !cps_lam. reflexivity. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The function [cpsv] satisfies the expected recurrence equations.  *)

Lemma cpsv_var:
  forall x,
  cpsv (Var x) = Var x.
Proof.
  reflexivity.
Qed.

Lemma cpsv_lam:
  forall t,
  cpsv (Lam t) = Lam (Lam (cps (lift 1 t) (O (Var 0)))).
Proof.
  intros. unfold cpsv, cpsinit. rewrite cps_lam. reflexivity.
Qed.

(* If [theta] is a renaming, then [theta x] is a variable, so [cpsv (theta x)]
   is [theta x], which can also be written [(Var x).[theta]]. *)

Lemma cpsv_var_theta:
  forall theta x,
  is_ren theta ->
  cpsv (theta x) = (Var x).[theta].
Proof.
  inversion 1. subst. asimpl. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* The tactic [cps] applies the rewriting rules [cps_value] and [cps_app] as
   many times as possible, therefore expanding applications of the function
   [cps] to values and to applications. *)

Ltac cps :=
  repeat first [ rewrite cps_value by obvious
               | rewrite cps_app | rewrite cps_let ].

(* -------------------------------------------------------------------------- *)

(* The translation of a value is a value. *)

(* In fact, thanks to the manner in which we have defined [cpsv], the image of
   every term through [cpsv] is a value. This turns out to be quite pleasant,
   as it allows removing nasty side conditions in several lemmas. *)

Lemma is_value_cpsv:
  forall v,
  (* is_value v -> *)
  is_value (cpsv v).
Proof.
  intros. destruct v; simpl; tauto.
Qed.

Hint Resolve is_value_cpsv : is_value obvious.

Hint Rewrite cpsv_var cpsv_lam : cpsv.
Ltac cpsv := autorewrite with cpsv.

(* -------------------------------------------------------------------------- *)

(* As a final step, we prove an induction principle that helps work with the
   functions [cpsv] and [cps]. When trying to establish a property of the
   function [cps], we often need to prove this property by induction on the
   size of terms. Furthermore, we usually need to state an auxiliary property
   of the function [cpsv] and to prove the two statements simultaneously, by
   induction on the size of terms. The following lemma is tailored for this
   purpose. It proves the properties [Pcpsv] and [Pcps] simultaneously. The
   manner in which the index [n] is used reflects precisely the manner in
   which each function depends on the other, with or without a decrease in
   [n]. The dependencies are as follows:

     [cpsv] invokes [cps] with a size decrease.

     [cps]  invokes [cpsv] without a size decrease and
                    [cps] with a size decrease.

   It is worth noting that this proof has nothing to do with the definitions
   of [cpsv] and [cps]. It happens to reflect just the right dependencies
   between them. *)

Lemma mutual_induction:
  forall
  (Pcpsv : term -> Prop)
  (Pcps : term -> continuation -> Prop),
  (forall n,
    (forall t c, size t < n -> Pcps t c) ->
    (forall v,   size v < S n -> Pcpsv v)
  ) ->
  (forall n,
    (forall v,   size v < S n -> Pcpsv v) ->
    (forall t c, size t < n -> Pcps t c) ->
    (forall t c, size t < S n -> Pcps t c)
  ) ->
  (
    (forall v,   Pcpsv v) /\
    (forall t c, Pcps t c)
  ).
Proof.
  intros Pcpsv Pcps IHcpsv IHcps.
  assert (fact:
    forall n,
    (forall v,   size v < n -> Pcpsv v) /\
    (forall t k, size t < n -> Pcps t k)
  ).
  { induction n; intros; split; intros;
    try solve [ false; lia ];
    destruct IHn as (?&?); eauto. }
  split; intros; eapply fact; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* In the proofs that follow, we never expand the definition of [cpsv] or
   [cps]: we use the tactics [cpsv] and [cps] instead. We actually forbid
   unfolding [cpsv] and [cps], so our proofs cannot depend on the details of
   the above definitions.

   In general, when working with complex objects, it is good practice anyway
   to characterize an object and forget how it was defined. Here, the
   functions [cpsv] and [cps] are characterized by the equations that they
   satisfy; the rest does not matter.

   Attempting to work with transparent [cpsv] and [cps] would be problematic
   for several reasons. The tactics [simpl] and [asimpl] would sometimes
   expand these functions too far. Furthermore, because we have used the term
   [smaller_wf_transparent] inside the definition of [cps], expanding this
   definition would often give rise to uncontrollably large terms. *)

Global Opaque cps cpsv.
