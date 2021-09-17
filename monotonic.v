Require Import Coq.Arith.PeanoNat.

Definition foo (x : nat) : nat :=
  x + 1.

Lemma monotonic_succ_foo :
  forall (x:nat), foo x + 1 > foo x.
Proof.
  intros.
  unfold foo.
  rewrite <- Nat.add_assoc.
  simpl.
  apply Nat.add_le_lt_mono.
  - reflexivity.
  - apply Nat.lt_succ_diag_r.
Qed.