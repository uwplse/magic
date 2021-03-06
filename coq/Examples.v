Require Import Arith NPeano.
Require Import Magic.Wand.

(* --- Geminio --- *)

Theorem obvious:
  forall n : nat,
    (nat * nat).
Proof.
  intros. geminio n. apply (n, n0).
Qed.

(* --- Sectumsempra --- *)

Theorem lt_S_m_p:
  forall n m p : nat, 
    n < m + S p -> n < S (p + m).
Proof.
  intros n m p H.
  rewrite <- Nat.add_succ_l.
  rewrite plus_comm.
  apply H.
Qed.

Sectumsempra lt_S_m_p.

Theorem test_lt_S_m_p_0:
  forall n m p : nat, 
    n < m + S p -> n < S p + m.
Proof.
  exact lt_S_m_p_0.
Qed.

Theorem test_lt_S_m_p_1:
  forall n m p : nat, 
    n < S p + m -> n < S (p + m).
Proof.
  exact lt_S_m_p_1.
Qed.

(* --- Levicorpus --- *)

Levicorpus lt_S_m_p.

Theorem test_lt_S_m_p_inv:
  forall n m p : nat, 
    n < S (p + m) -> n < m + S p.
Proof.
  exact lt_S_m_p_inv.
Qed.

(* --- Reducio --- *)

Theorem engorged:
  forall (a b : nat),
    a <= b ->
    a <= S b.
Proof.
  intros. rewrite plus_n_O. rewrite plus_comm.
  constructor. auto.
Qed.

Reducio engorged.

Theorem found_minimal_app:
  engorged_red = le_S.
Proof.
  reflexivity.
Qed.

(* --- Spells in combination --- *)

Theorem lt_S_m_p_iff:
  forall n m p : nat, 
    n < m + S p <-> n < S (p + m).
Proof.
  intros.
  geminio lt_S_m_p.
  levicorpus lt_S_m_p.
  constructor; auto.
Qed. 

