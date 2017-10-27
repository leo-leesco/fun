(* 22/09/2017. Someone asked during the course whether [~ (even 1)] can be
   proved, and if so, how. Here are several solutions, courtesy of
   Pierre-Evariste Dagand. *)

Inductive even: nat -> Prop :=
| even_O:
    even 0
| even_SS:
    forall n, even n -> even (S (S n)).

(* 1. The shortest proof uses the tactic [inversion] to deconstruct the
   hypothesis [even 1], that is, to perform case analysis. The tactic
   automatically finds that this case is impossible, so the proof is
   finished. *)

Lemma even1_v1:
  even 1 -> False.
Proof.
  inversion 1.
  (* In case you wish the see the proof term: *)
  (* Show Proof. *)
Qed.

(* For most practical purposes, the above proof *script* is good enough, and
   is most concise. However, those who wish to understand what they are doing
   may prefer to write a proof *term* by hand, in the Calculus of Inductive
   Constructions, instead of letting [inversion] construct a (possibly
   needlessly complicated) proof term. *)

(* 2. Generalizing with equality. *)

Lemma even1_v2':
  forall n, even n -> n = 1 -> False.
Proof.
  exact (fun n t =>
    match t with
    | even_O =>
      fun (q: 0 = 1) =>
        match q with (* IMPOSSIBLE *) end
    | even_SS n _ =>
      fun (q : S (S n) = 1) =>
        match q with (* IMPOSSIBLE *) end
    end
  ).
Qed.

Lemma even1_v2:
  even 1 -> False.
Proof.
  eauto using even1_v2'.
Qed.

(* 3. Type-theoretically, through a large elimination. *)

Lemma even1_v3':
  forall n,
  even n ->
  match n with
  | 0 => True
  | 1 => False
  | S (S _) => True
  end.
Proof.
  exact (fun n t =>
    match t with
    | even_O => I
    | even_SS _ _ => I
    end
  ).
Qed.

Lemma even1_v3:
  even 1 -> False.
Proof.
  apply even1_v3'.
Qed.

(* 3'. Same technique, using a clever [match ... in ... return]. *)

Lemma even1_v4':
  even 1 -> False.
Proof.
  exact (fun t =>
    match t in even n
      return (
        match n with
        | 0 => True
        | 1 => False
        | S (S _) => True
        end
        (* BUG: we need the following (pointless) type annotation *)
      : Prop)
    with
    | even_O => I
    | even_SS _ _ => I
    end
  ).
Qed.
