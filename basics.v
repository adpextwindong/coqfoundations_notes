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



