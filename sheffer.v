(* Sheffer 1913 states that any of the logical connectives
  for Boolean algebra can be implemented with the other using not and the logical connective.*)

Require Import Bool.

Example andb_orb : forall a b : bool,
  (* a ∧ b = ¬(¬a∨¬b) *)
  andb a b = negb(orb (negb a) (negb b)).
Proof.
  intros a b.
  destruct a.
  - simpl. rewrite -> negb_involutive. reflexivity.
  - auto.
Qed.

Search (negb (negb _)).

Example andb_implb : forall a b : bool,
  (* a ∧ b = ¬(a⇒¬b) *)
  andb a b = negb (implb a (negb b)).
Proof.
  intros a b.
  destruct a.
  - simpl. rewrite -> negb_involutive. reflexivity.
  - auto.
Qed.

Example orb_andb : forall a b: bool,
  (* a ∨ b	= ¬(¬a∧¬b) *)
  orb a b = negb (andb (negb a) (negb b)).
Proof.
  intros a b.
  destruct a.
  destruct b.
  - auto.
  - auto.
  - simpl. rewrite -> negb_involutive. reflexivity.
Qed.

Example orb_implb : forall a b: bool,
  (* a ∨ b = ¬a⇒b *)
  orb a b = implb (negb a) b.
Proof.
  intros a b.
  destruct a.
  - auto.
  - auto.
Qed.

Example implb_andb : forall a b: bool,
  (* a ⇒ b	¬(a∧¬b) *)
  implb a b = negb(andb a (negb b)).
Proof.
  intros a b.
  unfold implb.
  destruct a.
  - destruct b. auto. auto.
  - auto.
Qed.

Example implb_orb : forall a b : bool,
  (* a ⇒ b = ¬a∨b *)
  implb a b = orb (negb a) b.
Proof.
  intros a b.
  unfold implb.
  destruct a.
  - destruct b. auto. auto.
  - auto.
Qed.

Definition nandb (a: bool) (b: bool) : bool:=
  negb (andb a b).

Example nandb_tt : nandb true  true   = false. auto. Qed.
Example nandb_tf : nandb false true   = true. auto. Qed.
Example nandb_ft : nandb true  false  = true. auto. Qed.
Example nandb_ff : nandb false false  = true. auto. Qed.

Example xorb_andb : forall a b : bool,
(* (a ⊕ b) = ¬(¬(a ∧ ¬b) ∧ ¬(¬a ∧ b)) *)
  xorb a b = negb(andb (negb (andb a (negb b)))
                       (negb (andb (negb a) b))).
Proof.
  intros a b.
  unfold negb, xorb.
  destruct a.
  - destruct b. auto. auto.
  - destruct b. auto. auto.
Qed.

Example xorb_orb : forall a b : bool,
(* (a ⊕ b) = ¬(¬(¬a ∨ ¬b)∨ ¬(a∨b)) *)
  xorb a b = negb(orb (negb (orb (negb a) (negb b)))
                      (negb (orb a b))).
Proof.
  intros a b.
  unfold negb, xorb.
  destruct a.
  - destruct b. auto. auto.
  - destruct b. auto. auto.
Qed.

Example xorb_implb : forall a b : bool,
(* (a ⊕ b) = ¬((a ⇒ ¬b) ⇒ ¬(¬a ⇒ b)) *)
  xorb a b = negb ( implb (implb a (negb b))
                          (negb (implb (negb a) (b)))).
Proof.
  intros a b.
  unfold negb, implb, xorb.
  destruct a.
  - destruct b. auto. auto.
  - destruct b. auto. auto.
Qed.

Example nandb_negb : forall b : bool,
(* ¬b = b | b *)
  negb b = nandb b b.
Proof.
  unfold negb.
  destruct b.
  auto. auto.
Qed.

Example nandb_andb : forall a b : bool,
(* a ∧ b = (a | b) | (a | b) *)
  andb a b = nandb (nandb a b) (nandb a b).
Proof.
  intros a b.
  unfold nandb, andb, negb.
  destruct a.
  - destruct b. auto. auto.
  - auto.
Qed.

Example nandb_orb : forall a b : bool,
(* a ∨ b = (a | a) | (b | b) *)
  orb a b = nandb (nandb a a) (nandb b b).
Proof.
  intros a b.
  unfold nandb, andb, negb, orb.
  destruct a.
  - auto.
  - destruct b. auto. auto.
Qed.

Example nandb_implb1 : forall a b : bool,
(* a ⇒ b = (a | (b | b)) *)
  implb a b = nandb a (nandb b b).
Proof.
  intros a b.
  unfold nandb, implb, negb.
  destruct a.
  - destruct b. auto. auto.
  - auto.
Qed.

Example nandb_implb2 : forall a b : bool,
(* a ⇒ b = (a | (a | b)) *)
  implb a b = nandb a (nandb a b).
Proof.
  intros a b.
  unfold nandb, implb, negb.
  destruct a.
  - destruct b. auto. auto.
  - auto.
Qed.

Example nandb_eqb : forall a b : bool,
(*a <-> b = ((a | b) | ((a | a) | (b | b))) *)
  eqb a b = nandb (nandb a b) (nandb (nandb a a) (nandb b b)).
Proof.
  intros a b.
  unfold eqb, nandb, negb, andb.
  destruct a.
  - destruct b. auto. auto.
  - destruct b. auto. auto.
Qed.

Require Import ExtrHaskellBasic.
Extraction Language Haskell.
Extraction "nandeqb.hs" nandb_eqb.

(* TODO write the props in set. https://stackoverflow.com/questions/27175971/generating-haskell-code-from-coq-logical-or-arity-value-used#comment42848956_27176986*)
Require Import ExtrHaskellBasic.
