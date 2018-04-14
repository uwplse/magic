Require Import Arith NPeano.
Require Import Magic.Wand.

(* 
 * Test for the third exercise 3
 *)

Theorem lt_S_m_p:
  forall n m p : nat, 
    n < m + S p -> n < S (p + m).
Proof.
  intros n m p H.
  rewrite <- Nat.add_succ_l.
  rewrite plus_comm.
  apply H.
Qed.

Theorem test_lt_S_m_p_0:
  forall n m p : nat, 
    n < m + S p -> n < S p + m.
Proof.
  sectumsempra lt_S_m_p.
  auto.
Qed.
