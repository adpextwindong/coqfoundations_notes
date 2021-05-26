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

(* Peano Nats example from Intro to the CIC *)
Inductive N : Type :=
  | z : N
  | S : N -> N.

(* Slide 4 *)
(* https://fzn.fr/teaching/coq/ecole11/summer/lectures/lec9.pdf *)
Fixpoint psum (x:N) (y:N) : N :=
  match x, y with
  | z, _ => y
  | _, z => x
  | S (l), S (r) => psum (S (S (l)))  r
  end.

Compute (psum (S(z)) (S(z))).

Require Coq.extraction.Extraction.
Extraction Language Haskell.

(* From Coq Require Import Init.Nat. *)

Extraction "peano.hs" psum.
Recursive Extraction psum.

(* Require Import ZArith. 
  Binary encoded Nats exist in the library
*)