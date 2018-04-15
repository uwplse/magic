Require Import Arith NPeano.
Require Import Magic.Wand.

(*
 * Test for the seventh exercise.
 *)

Definition foo (n : nat) := n + 0.
Definition bar (n : nat) := n + (0 + 0).

Relashio 0 in foo.
Relashio 0 in bar.

Definition baz (m : nat) (n : nat) := n + m.

Theorem test_foo:
  baz = foo_rel.
Proof.
  reflexivity.
Qed.

Theorem test_bar:
  baz = bar_rel.
Proof.
  reflexivity.
Qed.
