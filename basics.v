(* Introducing a data type with the inductive *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* Function definition.
  Note it must have a total pattern match *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Compute (next_weekday thursday).

Example test_next_weekday:
  (next_weekday (next_weekday thursday)) = saturday.

Proof. simpl. reflexivity. Qed.

From Coq Require Export String.

Inductive bool : Type :=
  | true
  | false.

Definition negb (x: bool) : bool :=
  match x with
  | true => false
  | false => true
  end.

Definition andb (x: bool) (y: bool) : bool :=
  match x with
  | true => y
  | false => false
  end.

Definition orb (x: bool) (y: bool) : bool :=
  match x with
  | true => true
  | false => y
  end.

(*
Truth tables
*)

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

(* Introducing new symbolic notation for an existing definition *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* As bool type is not built in the if conditional
is generalized over any inductive type with two constructors

The true path is taken if the guard evaluates to the first constructor.*)

Definition negb' (x: bool) : bool :=
  if x then false
  else true.

Definition andb' (x: bool) (y: bool) : bool :=
  if x then y
  else false.

Definition orb' (x: bool) (y: bool) : bool :=
  if x then true
  else y.

(* Exercise 1 *)
Definition nandb (x: bool) (y: bool) : bool :=
  negb' (andb' x y).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise 2 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (b1 && b2) && (b2 && b3).

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* Types of an expression can be checked like this (similar to :t in ghci)*)

Check true.

Check negb.

(* A more interesting type constructor *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

(* We can then perform pattern matching on color in depth *)

Definition monochrome (c: color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition is_red (c: color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

(* Note that we can wild card on p in the color match*)

(* Module Declaration *)
Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

(* rgb b is scoped to the name Playground *)
Check Playground.b : rgb.
Check b: bool.

Module TuplePlayground.

Inductive bit : Type :=
  | B0
  | B1.

(* This is pretty much a tuple type *)
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0)
  : nybble.

(* Another example of pattern matching into a constructor *)

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).

Example allz1 : (all_zero (bits B1 B0 B1 B0)) = false.
Proof. simpl. reflexivity. Qed.

Example allz2 : (all_zero (bits B0 B0 B0 B0)) = true.
Proof. simpl. reflexivity. Qed.

End TuplePlayground.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

(* Interesting recursion on the structure of nat *)

Fixpoint even (n: nat) : bool :=
  match n with
  | O => true
  | S (O) => false
  | S (S (n)) => even n
end.

Example even1 : (even (S(S(S(S(O)))))) = true.
Proof. simpl. reflexivity. Qed.

(* Consider the fact that we're peeling S off n in these*)
Fixpoint plus (n m: nat) : nat :=
  match n with
  | O => m
  | S (n') => S (plus n' m)
end.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
end.

(*In this case its on power*)
Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
end.

End NatPlayground.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => mult (S n') (factorial (n'))
end.

(* Exercise 3*)
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

(* Nested matching *)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
    match m with
    | O => false
    | S m' => leb n' m'
    end
  end.

(*
Notation "x => y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
*)

(* Exercise 4 *)
Definition ltb (n m : nat) : bool :=
  (leb n m) && (negb (eqb n m)).

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Intros n handles the quantifier forall n and moves
   n from the goal to the context of current assumptions
 *)
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m: nat,
  n = m -> n + n = m + m.

(* Proof by Rewriting *)
Proof.
  (*move both n and m into the context of assumptions*)
  intros n m.
  (* move the hypothesis into the context: *)
  (* n = m from the theorem *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  (* rewrite <- H. Can be used to change the rewrite direction *)
  reflexivity. Qed.

(* Exercise 5 *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.

Proof.
  intros n m o.
  intros Hn.
  intros Ho.
  rewrite -> Hn.
  rewrite -> Ho.
  reflexivity. Qed.


(* Standard library proofs  *)

Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)
Check mult_n_Sm.
(* ===> forall n m : nat, n * m + n = n * S m *)

Theorem mult_n_0_m_0 : forall p q: nat,
  (p * 0) + (q * 0) = 0.

Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

(* Exercise 6 *)

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.

Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.

(* Proof by Case Analysis *)

(*
Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.
*)

(* eqb and + begin by performing a match on their first argument
but this compound expression n+1 is unknown and can't be simplified *)

(*Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false.
  Proof.
    intros n. destruct n as [| n'] eqn:E/
    - reflexivity.
    - reflexivity. Qed. *)

(* Destruct generates two subgoals for the cases where n = 0 and n = S n'.
   We solve these seperately. *)

Theorem negb_involutive : forall b: bool,
  negb(negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(* No as clause is needed because no variable binding is needed *)
(* The bullets '-' mark each subgoal case.*)

Theorem andb_commutative : forall b c,
  andb b c = andb c b.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(* Braces can also be used around each case *)

(*

  - destruct...
    { destruct...
    }
    { destruct...
    }
*)

(* Exercise 7*)

Lemma andb_tintro : forall a b : bool,
  a && b = (true && a) && b.
Proof.
  intros a b.
  destruct a.
  - simpl. reflexivity.
  - simpl. reflexivity. Qed.

(* How the book probably wants me to do it. *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  - simpl.
    intro H.
    rewrite <- H. reflexivity.
  - simpl.
    destruct c.
    + reflexivity.
    + intro H. rewrite -> H. reflexivity.
  Show Proof.
Qed.


(* We can use tautology on false = true in the 4th branch*)
Theorem andb_true_elim2_taut : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  - simpl.
    intro H.
    rewrite <- H. reflexivity.
  - simpl.
    destruct c.
    + reflexivity.
    + tauto.
  Show Proof.
Qed.

(* https://www.seas.upenn.edu/~cis500/cis500-f14/sf/ProofObjects.html *)
(* https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html *)
(* Discriminate on false = true *)
Theorem andb_true_elim2_discriminate : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  - simpl.
    intro H.
    rewrite <- H. reflexivity.
  - simpl.
    discriminate.
  Show Proof.
Qed.

(* intros x y. destruct y as [|y] eqn:E. *)

Theorem andb_true_elim2_SHORT : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b as [|b].
  - simpl.
    intro H.
    rewrite <- H. reflexivity.
  - simpl. destruct c.
    + reflexivity.
    + intro H. rewrite -> H. reflexivity.
  Show Proof.
Qed.


Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Datatypes.

(*Exercise 8*)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n. destruct n as [|n].
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

(* https://coq.inria.fr/refman/language/core/inductive.html#coq:cmd.Fixpoint *)

(* Fixpoint defintions must be "decreasing" on some argument to ensure termination*)

(* Exercise 9

This recursive function should terminate and return either n if m is zero or 500.
But because it doesn't decrease it gets rejected.

Fixpoint fooBad (n : nat) (m : nat) : nat :=
  match m with
  | 500 => m
  | O => n
  | S m' => fooBad n (S (S m'))
  end.
*)

(* Exercise 10 *)

(* https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html *)
(* Repeat tactic to apply rewrite -> H. multiple times *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x: bool), f x = x) -> forall (b: bool), f (f b) = b.
Proof.
  intros.
  repeat rewrite -> H. reflexivity.
Qed.

(* Generalized to f being an endomorphism *)
Theorem fixedpoint_twice :
  forall (f: Type -> Type),
    (forall (x :Type), f x = x) -> forall (y : Type), f (f y) = y.
Proof.
  intros.
  repeat rewrite -> H. reflexivity.
Qed.

(* Showcase repeat being used to apply the f x = x hypothesis multiple times *)
Example fixedpoint_three :
  forall (f: Type -> Type),
    (forall (x : Type), f x = x) -> forall (y : Type), f (f (f y)) = y.
Proof.
  intros.
  repeat rewrite -> H. reflexivity.
Qed.

(* Exercise 11 *)
Theorem negation_fn_applied_twice :
  forall (f: bool -> bool),
    (forall (x: bool), f x = negb x) ->
    forall (b: bool), f (f b) = b.
Proof.
  intros f H b.
  repeat rewrite -> H.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Exercise 12 *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros b.
  destruct b.
  - destruct c.
    + simpl. reflexivity.
    + simpl. intro H. rewrite -> H. reflexivity.
  - destruct c.
    + simpl. intro H. rewrite -> H. reflexivity.
    + simpl. reflexivity.
Qed.

(* Exercise 13 *)
Inductive bin: Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

(*

For example:
        decimal               binary                          unary
           0                       Z                              O
           1                    B1 Z                            S O
           2                B0 (B1 Z)                        S (S O)
           3                B1 (B1 Z)                     S (S (S O))
           4            B0 (B0 (B1 Z))                 S (S (S (S O)))
           5            B1 (B0 (B1 Z))              S (S (S (S (S O))))
           6            B0 (B1 (B1 Z))           S (S (S (S (S (S O)))))
           7            B1 (B1 (B1 Z))        S (S (S (S (S (S (S O))))))
           8        B0 (B0 (B0 (B1 Z)))    S (S (S (S (S (S (S (S O)))))))

Note that the low-order bit is on the left and the high-order bit is on the right -- the opposite of the way binary numbers are usually written. This choice makes them easier to manipulate.
*)

Fixpoint flopBits (m : bin) : bin :=
  match m with
  | Z => Z
  | B1 Z => B1 Z
  | B1 n' => B0 (flopBits n')
  | B0 n' => B0 (flopBits n')
  end.

Fixpoint allOnes (m : bin) : bool :=
  match m with
  | Z => true
  | B1 Z => true
  | B0 _ => false
  | B1 n' => true && allOnes n'
  end.


Fixpoint buildNBZeroes (n:nat) (tail : bin) : bin :=
  match n with
  | 0 => tail
  | S n' => B0 (buildNBZeroes n' tail)
end.

Compute buildNBZeroes 4 (B1 Z).

Fixpoint seekForZeroFlipAndTail (m : bin) (seeked : nat) : bin :=
  match m with
  | Z => m
  | B1 Z => m
  | B0 Z => m
  | B0 n' => buildNBZeroes seeked (B1 n')
  | B1 n' => seekForZeroFlipAndTail n' (seeked + 1)
end.

Definition incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 Z => B1 Z
  | B1 Z => B0 (B1 Z)
  | _ => match allOnes m with
         | true => B0 (flopBits m)
         | false => seekForZeroFlipAndTail m 0
      end
end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof.
  simpl. reflexivity.
Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof.
  simpl. reflexivity.
Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof.
  simpl. reflexivity.
Qed.

Example test_bin_incr4 : incr (B1 (B0 (B1 Z))) = B0 (B1 (B1 Z)).
Proof.
  simpl. reflexivity.
Qed.

Example test_bin_incr5 : incr (B0 (B1 (B1 Z))) = B1 (B1 (B1 Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr6 : incr (B1 (B1 (B1 (B0 (B1 (B0 (B1 (Z)))))))) = B0 (B0 (B0 (B1 (B1 (B0 (B1 Z)))))).
Proof. simpl. reflexivity. Qed.

Fixpoint bnAUX (m : bin) (bit : nat) : nat :=
  match m with
  | Z => 0
  | B1 Z => bit
  | B0 Z => bit
  | B0 n' => bnAUX n' (bit * 2)
  | B1 n' => bit + bnAUX n' (bit * 2)
end.

Definition bin_to_nat (m:bin) : nat :=
  bnAUX m 1.

Example test_bna_0 : bin_to_nat (Z) = 0.
Proof. unfold bin_to_nat. unfold bnAUX. reflexivity. Qed.

Example test_bna_1 : bin_to_nat (B1 Z) = 1.
Proof. unfold bin_to_nat. unfold bnAUX. reflexivity. Qed.

Example test_bna_3 : bin_to_nat (B1 (B1 Z)) = 3.
Proof. unfold bin_to_nat. unfold bnAUX. reflexivity. Qed.

Example test_bna_4 : bin_to_nat (B0 (B0 (B1 Z))) = 4.
Proof. unfold bin_to_nat. unfold bnAUX. reflexivity. Qed.


Example test_bin_nat7 : bin_to_nat (B1 (B1 (B1 Z))) = 7.
Proof.
  unfold bin_to_nat. unfold bnAUX.
  simpl.
  reflexivity.
Qed.

Example test_bin_nat1 : bin_to_nat (B0 (B1 Z)) = 2.
Proof.
  simpl.
  unfold bin_to_nat. unfold bnAUX.
  reflexivity.
Qed.

Example test_bin_nat2 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. unfold bin_to_nat. unfold bnAUX. reflexivity. Qed.

Example test_bin_nat3 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. unfold bin_to_nat. unfold bnAUX. reflexivity. Qed.
