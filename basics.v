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
Definition nandb (x: bool) (y: bool) : bool
  . Admitted.

Example test_nandb1: (nandb true false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb2: (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3: (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4: (nandb true true) = false.
(* FILL IN HERE *) Admitted.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Example test_andb31: (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.
Example test_andb32: (andb3 false true true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb33: (andb3 true false true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb34: (andb3 true true false) = false.
(* FILL IN HERE *) Admitted.

