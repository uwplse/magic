Require Import Arith NPeano.
Require Import Magic.Wand.

(*
 * Test for the sixth exercise.
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

Reducio Maxima engorged.

Theorem found_minimal_app:
  engorged_red = le_S.
Proof.
  reflexivity.
Qed.

(* --- Cycles --- *)

Theorem engorged2:
  forall (a b : nat),
    a <= b ->
    a <= S (S (b + 0)).
Proof.
  intros.
  constructor.
  rewrite plus_n_O.
  rewrite plus_Snm_nSm.
  rewrite plus_comm.
  rewrite plus_0_r.
  constructor.
  auto.
Qed.

Sectumsempra engorged2.

(* 
 * Simplified factor types, for reference:
 * 
 * 0. a <= b -> a <= S b 
 * 1. a <= S b -> a <= S (b + 0)
 * 2. a <= S (b + 0) -> a <= b + 0 + 1
 * 3. a <= b + 0 + 1 -> a <= S (b + 0 + 0) 
 * 4. a <= S (b + 0 + 0) -> a <= S (b + 0) 
 * 5. a <= S (b + 0) -> a <= S (S (b + 0))
 * 
 * Or, in other words:
 *
 * 0. A -> B 
 * 1. B -> C
 * 2. C -> D
 * 3. D -> E
 * 4. E -> C 
 * 5. C -> F
 *)

Reducio Maxima engorged2.

Theorem reduced2:
  forall (a b : nat),
    a <= b ->
    a <= S (S (b + 0)).
Proof.
  intros.
  constructor.
  rewrite plus_0_r.
  constructor.
  auto.
Defined.

Theorem found_minimal_app2:
  engorged2_red = reduced2.
Proof.
  reflexivity.
Qed.


