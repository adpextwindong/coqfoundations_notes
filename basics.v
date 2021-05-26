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
