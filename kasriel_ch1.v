Require Import Bool.

Example excercise1: forall p q : bool,
  (* Show that this is a tautology *)
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

(* TODO

Theorem exercise1_prop : forall p q : Prop,
  (~q -> ~p) -> (p -> q).
Proof.
  intros p q.
  intro H.
Admitted.

I'll have to learn more about the Prop type in Coq...

 *)

Example exercise2: forall p q r : bool,
(* ((p -> q) /\ (q -> r)) -> (p -> r) *)
  implb (andb (implb p q) (implb q r))
        (implb p r) = true.
Proof.
  intros.
  induction p.
  simpl.
  - destruct q.
    + simpl. induction r. auto. auto.
    + auto.
  - simpl. induction q. induction r. auto. auto. auto.
Qed.

Example excerise3: forall p q : bool,
  implb (andb p q) (orb p q) = true.
Proof.
  intros.
  destruct p.
  - simpl. destruct q. auto. auto.
  - simpl. auto.
Qed.

Example exercise4: forall p q : bool,
  implb (negb (andb p q))
        (orb (negb p) (negb q)) = true.
Proof.
  intros.
  destruct p.
  - simpl. destruct q. simpl. auto. simpl. auto.
  - simpl. destruct q. simpl. auto. simpl. auto.
Qed.

Example exercise4_aux:
  forall p q, (andb p q) = false -> orb (negb p) (negb q) = true.
Proof.
  intros p q H.
  rewrite <- negb_andb.
  apply negb_true_iff.
  apply H.
Qed.

Search (negb _ = true).
Search (negb _ || negb _).