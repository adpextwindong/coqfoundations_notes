Require Import Bool.

Theorem excercise1: forall p q : bool,
  implb (implb (negb q) (negb p)) (implb p q) = true.
Proof.
  intros p q.
  induction p.
  - destruct q.
    + reflexivity.
    + reflexivity.
  - destruct q.
    + reflexivity.
    + reflexivity.
Qed.

(* TODO *)
Theorem exercise1_prop : forall p q : Prop,
  (~q -> ~p) -> (p -> q).
Proof.
  intros p q.
  intro H.
Admitted.