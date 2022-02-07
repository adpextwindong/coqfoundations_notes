From LF Require Export Basics.


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

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n as [| n' IHn'].
  - reflexivity.
  - destruct n'.
    + simpl. reflexivity.
    + simpl.
      apply eq_S.
      repeat rewrite <- plus_Sn_m.
      rewrite -> IHn'. reflexivity.
Qed.

(*Searchs that resulted the used theorems

Search (S (_ + _ + _) = S _ + _).
Search (S _ + _ = S _).
Search (_ + _ = S _ + _ ).

*)

(*
Exercise: 2 stars, standard (double_plus)
Consider the following function, which doubles its argument:
Use induction to prove this simple fact about double:
*)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intro n.
  induction n as [| n' IHn'].
  - unfold double. simpl. reflexivity.
  - simpl.
    apply eq_S.
    rewrite -> PeanoNat.Nat.add_succ_r.
    apply eq_S.
    rewrite -> IHn'. reflexivity.
Qed.

Fixpoint even (n: nat) : bool :=
  match n with
  | O => true
  | S (O) => false
  | S (S (n)) => even n
end.

(* Exercise: 2 stars, standard, optional (even_S)

One inconvenient aspect of our definition of even n is the recursive call on n - 2. This makes proofs about even n harder when done by induction on n, since we may need an induction hypothesis about n - 2. The following lemma gives an alternative characterization of even (S n) that works better with induction: *)


Lemma doubleEven : forall n : nat,
  even (S (S n)) = even n.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma doubleNegb : forall n : nat,
  negb (negb (even n)) = even n.
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - destruct (even (S n)).
    simpl. reflexivity.
    simpl. reflexivity.
Qed.


Lemma evenSOut : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - rewrite doubleEven.
    rewrite -> IHn.
    rewrite <- doubleEven.
    rewrite -> doubleEven.
    rewrite doubleNegb.
    reflexivity.
Qed.


Search (_ = _ -> S _ = S _).

Lemma dropNegb_s : forall n : nat,
   negb (even (S n)) = even n.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> doubleEven.
    rewrite -> evenSOut.
    destruct n'.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intro n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> doubleEven.
    rewrite -> dropNegb_s.
    reflexivity.
Qed.

(* Destruct vs Induction tactic

Destruct forces you to analyse indepedent cases.

For example if you have an unknown Bool, you can destruct on it to do equational reasoning in both the true and false case.

Induction however is used when you need to exhaust cases that destruct can't handle.

For example if you destruct on a peano nat you'll corner yourself into destructing on n'. This leads you to an identical subgoal if you don't use induction.

With Induction you can rejigger your goal into a form that you can apply the induction hypothesis. *)

Lemma plus0 (x: nat) : x + 0 = x.
Proof.
  induction x.
  - auto.
  - simpl. rewrite IHx. reflexivity.
Qed.

Theorem commutnat (x y:nat) : x + y = y + x.
Proof.
  induction x as [| x' IHx'].
  - simpl. rewrite plus0. reflexivity.
  - simpl. rewrite -> IHx'.
           rewrite <- plus_n_Sm. reflexivity.
Qed.

(*
For any x y
 x + y = y + x

By induction on x.
- Assume x = 0
    0 + y = y + 0
By definition of plus
  y = y + 0
By the lemma that x + 0 = x
  y = y

- Assume x = S x', where
    x' + y = y + x'
  we must show that
    S x' + y = y + S x'
  By definition of plus on the lhs
    S (x' + y) = y + S x'
  Then by the induction hypothesis on the lhs
    S (x' + y) = y + S x'
  And by the definition of plus on the rhs
    S (y + x') = S (y + x')
Qed.
*)

(*
For any n,
 (n =? n) = true
By induction on n
- Assume n = 0
  (0 =? 0) = true
  Is trivial by defn of =?

- Assume n = S n', where
    (n' =? n')
  We must show that
    (S n') =? (S n') = true

  By definition of =?, this follows from
    n' =? n' = true

  which is immediate by the induction hyptohesis
*)

Theorem leb_refl : forall n : nat,
  (n <= n).
Proof.
  intros n.
  apply le_n.
Qed.

(*
To see whats applied by auto.

Show Proof.
auto.
Show Proof.
*)

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.


Theorem zero_neqb_S : forall n : nat,
  (0 =? (S n)) = false.
Proof.
  reflexivity.
Qed.

Theorem andb_false_r : forall b: bool,
  andb b false = false.
Proof.
  intro b; destruct b; reflexivity.
Qed.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros.
  induction p.
  - simpl. apply H.
  - simpl. apply IHp.
Qed.

Theorem S_neqb_0 : forall n: nat,
  (S n) =? 0 = false.
Proof.
  reflexivity.
Qed.

Theorem mult_1_l : forall n: nat,
  1 * n = n.
Proof.
  simpl. apply plus0.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros.
  destruct b; simpl; destruct c; reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n. reflexivity.
          simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p: nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  induction n.
  - auto.
  - simpl. rewrite IHn. apply plus_assoc.
Qed.



