Require Import Arith NPeano.
Require Import Magic.Wand.

(*
 * Test for the second exercise.
 *)

Definition f (x : nat) :=
  S (S x).

Geminio f.

Theorem test_geminio:
  f = f_clone.
Proof.
  reflexivity.
Qed.
