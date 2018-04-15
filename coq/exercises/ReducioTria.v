Require Import Arith NPeano.
Require Import Magic.Wand.

(*
 * Test for the fifth exercise.
 *)

(* --- Regresssion test --- *)

Theorem engorged:
  forall (a b : nat),
    a <= b ->
    a <= S b.
Proof.
  intros. rewrite plus_n_O. rewrite plus_comm.
  constructor. auto.
Qed.

Reducio Tria engorged.

Theorem found_minimal_app:
  engorged_red = le_S.
Proof.
  reflexivity.
Qed.

(* --- Nested inverses --- *)

Theorem engorged2:
  forall (a b : nat),
    a <= b ->
    a <= S b.
Proof.
  intros.
  rewrite <- plus_0_r. 
  rewrite plus_n_O.
  rewrite plus_0_r.
  rewrite plus_comm.
  constructor. 
  auto.
Qed.

Reducio Tria engorged2.

Theorem found_minimal_app2:
  engorged2_red = le_S.
Proof.
  reflexivity.
Qed.
