Import Coq.Init.Nat.

(* Page 25 Example 3 *)

Fixpoint sum_one (n : nat) : nat :=
  match n with
    | O => O
    | S i => 1 + sum_one i
 end.

Example test_5: sum_one 5 = 5.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem sum_one_equals_n (n : nat) : sum_one n = n.
Proof.
  intros.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Print sum_one_equals_n.

(*

sum_one_equals_n = 
fun n : nat =>
nat_ind (fun n0 : nat => sum_one n0 = n0) eq_refl
  (fun (n' : nat) (IHn' : sum_one n' = n') => eq_ind_r (fun n0 : nat => S n0 = S n') eq_refl IHn') n
     : forall n : nat, sum_one n = n

*)

(* Page 25 Example 2 *)

Fixpoint sum_k (n : nat) : nat :=
  match n with
    | O => O
    | S i => n + sum_k i
 end.

Theorem gauss_nats (n : nat) : sum_k n = (n * (n + 1))/ 2.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - Admitted. (*TODO, we need a rewrite apporach like in mathcomp*)

