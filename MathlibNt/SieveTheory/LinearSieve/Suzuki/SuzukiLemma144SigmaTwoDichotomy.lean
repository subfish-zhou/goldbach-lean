import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence


open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

set_option maxHeartbeats 1600000

/-!
# Lemma 14.4, Case I successor: real-`τ` / `Σ₂` frontier

This file keeps Suzuki's literal
`τ = max s ((1 - log 2 / log D)⁻¹)`.  In particular it does not use the
incorrect simplification `τ = s` to erase `Σ₂`.

The exact finite recurrence, the global-IH instantiation, the internal `Σ₀`
endpoint, the natural-ceiling `Σ₁₂` theorem, and Claim (14.13) all compile in
the current import cone.  The theorem below closes the elementary carrier
part of the genuine `Σ₂` dichotomy: the sum is either in the even, nonempty
narrow branch, or is literally zero.
-/

/-- The source correction occurring in the upper splitting point of (14.9). -/
noncomputable def lemma144RealTau (D : ℕ) (s : ℝ) : ℝ :=
  max s ((1 - Real.log 2 / Real.log (D : ℝ))⁻¹)

/-- A source-faithful description of the only branch in which `Σ₂` still
requires (14.22).  `upper_lt_z` says that the upper split point lies strictly
below the sieve endpoint; `even_depth` records the source parity conclusion. -/
structure Lemma144SigmaTwoEvenNarrow (N D z : ℕ) (s : ℝ) : Prop where
  even_depth : Even N
  upper_lt_z :
    (D : ℝ) ^ (1 / lemma144RealTau D s) < (z : ℝ)

/-- If source geometry rules out a nonempty upper carrier at odd depth, then
with the real `τ` the actual `Σ₂` is either the genuine even narrow branch or
zero.  No estimate for `Σ₂` is assumed here. -/
theorem lemma144_sigmaTwo_evenNarrow_or_zero
    (S : BoundingSieve) {N D z : ℕ} {s : ℝ}
    (hoddEmpty : ¬ Even N →
      (z : ℝ) ≤ (D : ℝ) ^ (1 / lemma144RealTau D s)) :
    Lemma144SigmaTwoEvenNarrow N D z s ∨
      suzukiSigmaTwo S N D z
        ((D : ℝ) ^ (1 / lemma144RealTau D s)) = 0 := by
  classical
  have hzero (hupper : (z : ℝ) ≤ (D : ℝ) ^ (1 / lemma144RealTau D s)) :
      suzukiSigmaTwo S N D z
        ((D : ℝ) ^ (1 / lemma144RealTau D s)) = 0 := by
    unfold suzukiSigmaTwo
    apply Finset.sum_eq_zero
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpz : p < z := (Finset.mem_filter.mp hp'.1).2
    have hpzR : (p : ℝ) < (z : ℝ) := by exact_mod_cast hpz
    have hzp : (z : ℝ) ≤ (p : ℝ) := hupper.trans hp'.2
    exact False.elim ((not_le_of_gt hpzR) hzp)
  by_cases hN : Even N
  · by_cases hnarrow :
      (D : ℝ) ^ (1 / lemma144RealTau D s) < (z : ℝ)
    · exact Or.inl ⟨hN, hnarrow⟩
    · exact Or.inr (hzero (le_of_not_gt hnarrow))
  · exact Or.inr (hzero (hoddEmpty hN))


end MathlibNt.SieveTheory
