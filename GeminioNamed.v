Require Import Arith NPeano.
Require Import Magic.Wand.

(*
 * Test for the first exercise.
 *)

Definition f (x : nat) :=
  S (S x).

Geminio f as g.

Theorem test_geminio:
  f = g.
Proof.
  reflexivity.
Qed.
