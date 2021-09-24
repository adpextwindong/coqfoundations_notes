From LF Require Export Basics.
Require Import Coq.Program.Tactics.

(* Reflexivity can't be applied since n in n + 0 is an arbitrary unknown, so match on + can't be simpl. *)

Theorem add_0_r_firstry : forall n: nat,
  n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.

Theorem add_0_r_secondtry : forall n : nat,
  n + 0 = n.
  intros n . destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl.
    (* Stuck at S (n' + 0) = S n'*)
Abort.

(* We can't destruct on n because the succ case will get stuck in the same way.

Since n can be arbitrarily large we can't destruct on n' in that case either. This forces us to induct on n.

We can use the induction tactic.*)

Theorem add_0_r : forall n: nat,
  n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n'*)
    simpl. (* Now we can apply the induction hypothesis *)
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Exercise: 2 stars, standard, especially useful (basic_induction)

Prove the following using induction. You might need previously proven results.*)

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n'*)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'.
    induction m as [| m' IHm'].
    + simpl. reflexivity.
    + reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - induction m as [| m' IHm'].
    + reflexivity.
    + apply plus_n_O.
  - simpl. rewrite <- plus_n_Sm.
    apply eq_S.
    rewrite -> IHn'. reflexivity.
Qed.

(* These applied theorems were found using these queries

Search (_ = _ -> S _ = S _).
Search (_ + S _).
Search (_ + 0).
*)

  (* FILL IN HERE *) Admitted.
Theorem add_assoc : ∀ n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.
☐
