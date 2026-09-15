/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969Theorem1FiniteChain

/-!
# Richert 1969, hypothesis (A4) and the squareful payment

Frozen source:

* `references/richert-1969/richert-1969.pdf`, PDF pages 2 and 10,
  hypothesis (A4) and equation (3.7);
* `references/richert-1969/VISION_TRANSCRIPTION.md`, sections 1 and 5.

This file identifies the carrier removed by the prime on Richert's weighted
sum with a finite union of the `p^2 ∣ a` fibres.  Hypothesis (A4) is then
applied fibre by fibre.  No sieve fundamental lemma is used here.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace MathlibNt.SieveTheory.Richert1969

/-- Richert's literal whole-sequence fibre `A[p^2]` in hypothesis (A4). -/
def wholeSquareDivisibleCarrier (A : Finset ℕ) (p : ℕ) : Finset ℕ :=
  A.filter fun a => p ^ 2 ∣ a

/-- The `p^2 ∣ a` fibre occurring on the left side of Richert's (A4). -/
def squareDivisibleCarrier (A : Finset ℕ) (P p : ℕ) : Finset ℕ :=
  (lowerCarrier A P).filter fun a => p ^ 2 ∣ a

/-- Sifting only restricts the literal whole-sequence (A4) fibre. -/
theorem squareDivisibleCarrier_subset_whole
    (A : Finset ℕ) (P p : ℕ) :
    squareDivisibleCarrier A P p ⊆ wholeSquareDivisibleCarrier A p := by
  intro a ha
  rcases Finset.mem_filter.mp ha with ⟨haLower, hpSq⟩
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp haLower).1, hpSq⟩

/-- The union of the square-divisible fibres removed by the prime on (3.1). -/
def squarefulRemovedCarrier (A Q : Finset ℕ) (P : ℕ) : Finset ℕ :=
  Q.biUnion fun p => squareDivisibleCarrier A P p

theorem squarefulRemovedCarrier_eq_sdiff
    (A Q : Finset ℕ) (P : ℕ) :
    squarefulRemovedCarrier A Q P =
      lowerCarrier A P \ squarefreeWeightedCarrier A Q P := by
  ext a
  simp only [squarefulRemovedCarrier, squareDivisibleCarrier,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_sdiff,
    squarefreeWeightedCarrier]
  constructor
  · rintro ⟨p, hpQ, haLower, hpSq⟩
    exact ⟨haLower, fun haGood => (haGood.2 p hpQ) hpSq⟩
  · rintro ⟨haLower, haNotGood⟩
    have hnot : ¬∀ p ∈ Q, ¬p ^ 2 ∣ a := by
      intro hall
      exact haNotGood ⟨haLower, hall⟩
    push Not at hnot
    obtain ⟨p, hpQ, hpSq⟩ := hnot
    exact ⟨p, hpQ, haLower, hpSq⟩

/-- The exact squareful correction is the cardinality of the union of the
`p^2` fibres, not a separate analytic error term. -/
theorem squarefulCorrection_eq_removedCarrier_card
    (A Q : Finset ℕ) (P : ℕ) :
    squarefulCorrection A Q P =
      ((squarefulRemovedCarrier A Q P).card : ℝ) := by
  have hsubset :
      squarefreeWeightedCarrier A Q P ⊆ lowerCarrier A P :=
    Finset.filter_subset _ _
  rw [squarefulCorrection, squarefulRemovedCarrier_eq_sdiff,
    Finset.card_sdiff_of_subset hsubset,
    Nat.cast_sub (Finset.card_le_card hsubset)]

/-- The finite union bound which turns the squareful correction into the sum
of the individual (A4) carriers. -/
theorem squarefulCorrection_le_sum_squareDivisibleCarrier
    (A Q : Finset ℕ) (P : ℕ) :
    squarefulCorrection A Q P ≤
      ∑ p ∈ Q, ((squareDivisibleCarrier A P p).card : ℝ) := by
  rw [squarefulCorrection_eq_removedCarrier_card]
  exact_mod_cast (Finset.card_biUnion_le :
    (Q.biUnion fun p => squareDivisibleCarrier A P p).card ≤
      ∑ p ∈ Q, (squareDivisibleCarrier A P p).card)

/-- Richert's hypothesis (A4), restricted to the weighted prime carrier used
in Theorem 1. -/
def SquarefulA4On
    (A Q : Finset ℕ) (X A4 : ℝ) : Prop :=
  ∀ p ∈ Q,
    ((wholeSquareDivisibleCarrier A p).card : ℝ) ≤
      A4 * (X * Real.log X / (p : ℝ) ^ 2 + 1)

/-- Direct use of (A4) in (3.7): the removed carrier is paid by summing the
literal `A4 * (X log X / p^2 + 1)` bounds over the weighted prime interval. -/
theorem squarefulCorrection_le_sum_A4
    (A Q : Finset ℕ) (P : ℕ) (X A4 : ℝ)
    (hA4 : SquarefulA4On A Q X A4) :
    squarefulCorrection A Q P ≤
      ∑ p ∈ Q, A4 * (X * Real.log X / (p : ℝ) ^ 2 + 1) := by
  exact (squarefulCorrection_le_sum_squareDivisibleCarrier A Q P).trans
    (Finset.sum_le_sum fun p hp =>
      (by
        exact_mod_cast Finset.card_le_card
          (squareDivisibleCarrier_subset_whole A P p) :
        ((squareDivisibleCarrier A P p).card : ℝ) ≤
          (wholeSquareDivisibleCarrier A p).card).trans
        (hA4 p hp))

/-- The literal Theorem 1 specialization of the preceding (A4) payment. -/
theorem theoremOneSquarefulCorrection_le_sum_A4
    (A : Finset ℕ) (X : ℝ) (K : ℕ) (v u A4 : ℝ)
    (hA4 : SquarefulA4On A (theoremOneWeightedPrimes X K u v)
      X A4) :
    squarefulCorrection A (theoremOneWeightedPrimes X K u v)
        (theoremOneSiftingProduct X K v) ≤
      ∑ p ∈ theoremOneWeightedPrimes X K u v,
        A4 * (X * Real.log X / (p : ℝ) ^ 2 + 1) :=
  squarefulCorrection_le_sum_A4 A
    (theoremOneWeightedPrimes X K u v)
    (theoremOneSiftingProduct X K v) X A4 hA4

end MathlibNt.SieveTheory.Richert1969
