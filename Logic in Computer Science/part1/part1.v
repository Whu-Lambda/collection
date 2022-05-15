Require Import ZArith.
Require Import ZArith.Zorder.
Require Import Bool.
Require Import Unicode.Utf8.
Require Import Setoid.
Require Import Lia.
Set Implicit Arguments.
Open Scope Z_scope.

(* Example 1 *)

Theorem ex_1 : ∀ a b c : Z, 
  c = (a + b)^2 -> c = a^2 + 2 * a * b + b^2.
Proof.
  intros a b c H.
  rewrite H.
  ring_simplify.
  reflexivity.
Qed.

(* Example 2 *)

Theorem ex_2 : ∀ a b a0 b0 a1 b1 a2 : Z, a0 = a /\ b0 = b /\ 
  a1 = a + b /\ b1 = a1 - b /\ a2 = a1 - b1 -> 
  a2 = b0 /\ b1 = a0.
Proof.
  intros a b a0 b0 a1 b1 a2 [HA0 [HB0 [HA1 [HB1 HA2]]]].
  split.
  - rewrite HB1 in HA2. 
    ring_simplify in HA2.
    rewrite <- HB0 in HA2.
    auto.
  - rewrite HA1 in HB1.
    ring_simplify in HB1.
    rewrite <- HA0 in HB1.
    auto.
Qed.

(* Example 3 *)

Lemma helper : ∀ a b : Z, a < b -> b >= a.
Proof.
  intros a b H.
  lia.
Qed.

Theorem ex_3_part1 : ∀ a1 a2 a11 a21 a12 : Z, a1 < a2 /\ a11 = a1 + a2 /\ 
  a21 = a11 - a2 /\ a12 = a11 - a21 -> 
  a12 >= a21.
Proof.
  intros a1 a2 a11 a21 a12 [HA1 [HA11 [HA21 HA12]]].
  rewrite HA12. rewrite HA21.
  rewrite HA11. ring_simplify.
  apply helper in HA1. apply HA1.
Qed.

Theorem ex_3_part2 : ∀ a1 a2 : Z, a1 >= a2 -> a1 >= a2.
Proof.
  trivial.
Qed.

(* Example 4 *)

Theorem ex_4 : ∀ i N : Z, i <= N /\ i >= N -> i = N.
Proof.
  intros i N [HI1 HI2].
  lia.
Qed.
