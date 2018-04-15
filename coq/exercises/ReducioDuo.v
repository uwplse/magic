Require Import Arith NPeano.
Require Import Magic.Wand.

(*
 * Test for the fourth exercise.
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

Reducio Duo engorged.

Theorem found_minimal_app:
  engorged_red = le_S.
Proof.
  reflexivity.
Qed.

(* --- Identity type in path --- *)

Theorem engorged2:
  forall (n m : nat),
    n < n + S m ->
    n < S n + m.
Proof.
  intros. 
  rewrite Nat.add_succ_l.
  rewrite <- Nat.add_succ_r.
  auto.
Qed.

Sectumsempra engorged2.

Reducio Duo engorged2.

Theorem found_minimal_app2:
  engorged2_red = engorged2_0.
Proof.
  reflexivity.
Qed.

(* --- Identity type between inverses --- *)

Theorem engorged3:
  forall (a b : nat),
    a <= b ->
    a <= S b.
Proof.
  intros. 
  rewrite plus_n_O.
  rewrite Nat.add_succ_l.
  rewrite plus_comm.
  constructor. 
  auto.
Qed.

Sectumsempra engorged3.

Reducio Duo engorged3.

Theorem found_minimal_app3:
  engorged3_red = engorged3_0.
Proof.
  reflexivity.
Qed.