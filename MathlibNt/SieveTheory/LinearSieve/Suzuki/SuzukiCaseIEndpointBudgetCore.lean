import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ExplicitRemaindersSourceOrder
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Remainder1423

namespace MathlibNt.SieveTheory

open SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Pointwise normalization of the Claim-14.5 endpoint into the budget at `s`.
The Claim-14.6 transport is supplied at this same `D`; no new eventual cutoff
is selected here. This applies to both the strict Case-I range and `s = 2`. -/
theorem caseI_claim145Scale_le_transported_remainderUnit
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D : ℕ} {C CB K d Δ s : ℝ}
    (hH : Section13HatSourceContract H) (hD3 : 3 ≤ D)
    (hC : 0 < C) (hCB : 0 ≤ CB) (hs : 1 ≤ s)
    (hsσ : s ≤ sourceSigma (D : ℝ) d)
    (htransport : errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d) ≤
      errorEnvelope H N (D : ℝ) d s) :
    CB * claim14_5Scale S H N (D : ℝ) d Δ
        (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) ≤
      (CB / C) * caseI1423RemainderUnit
        (sigma12InheritedBudget S H N D ⌈(D : ℝ) ^ (1 / s)⌉₊ C K d Δ s)
        (D : ℝ) (sourceSigma (D : ℝ) d) := by
  have hD : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hlog := Real.log_pos hD
  have hll : 0 < Real.log (Real.log (D : ℝ)) := by
    apply Real.log_pos
    apply (Real.lt_log_iff_exp_lt (zero_lt_one.trans hD)).2
    exact (show Real.exp 1 < 3 by linarith [Real.exp_one_lt_d9]).trans_le
      (by exact_mod_cast hD3)
  have hσ : 0 < sourceSigma (D : ℝ) d := zero_lt_one.trans_le (hs.trans hsσ)
  have hzD : (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) ≤ (D : ℝ) := by
    have hroot : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hD.le
          ((div_le_one (zero_lt_one.trans_le hs)).2 hs)
    exact_mod_cast (Nat.ceil_le.mpr hroot)
  have hsource := caseISigmaZeroDirectRemainder_le_sourceOrder S H
    (N := N) (C := C) (C145 := CB) (K := K) (Δ := Δ)
    hD hll (by linarith [Real.log_le_sub_one_of_pos hlog]) hzD hσ hC hCB
    (errorEnvelope_nonneg H N hD hσ.le (hH.positive _ _ hσ).le)
  have hbudget :
      sigma12InheritedBudget S H N D ⌈(D : ℝ) ^ (1 / s)⌉₊ C K d Δ
          (sourceSigma (D : ℝ) d) ≤
        sigma12InheritedBudget S H N D ⌈(D : ℝ) ^ (1 / s)⌉₊ C K d Δ s := by
    unfold sigma12InheritedBudget
    have hV := suzukiVProduct_pos S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ)
    exact mul_le_mul_of_nonneg_left htransport (by positivity)
  have hcoef : 0 ≤ caseISourceOrderCoefficient (CB / C) (D : ℝ) d := by
    unfold caseISourceOrderCoefficient
    exact div_nonneg (div_nonneg hCB hC.le) (mul_nonneg hll.le hσ.le)
  exact hsource.trans (by
    convert mul_le_mul_of_nonneg_left hbudget hcoef using 1
    simp only [caseISourceOrderCoefficient, caseI1423RemainderUnit]
    ring)

/-- Add the three independently paid endpoint terms and spend their combined
source-order coefficient against the remaining contraction budget. -/
theorem caseI_three_remainders_le_gap
    {x₀ x₁ x₂ a₀ a₁ a₂ B D d ρ : ℝ} (hB : 0 ≤ B)
    (h₀ : x₀ ≤ a₀ * caseI1423RemainderUnit B D (sourceSigma D d))
    (h₁ : x₁ ≤ a₁ * caseI1423RemainderUnit B D (sourceSigma D d))
    (h₂ : x₂ ≤ a₂ * caseI1423RemainderUnit B D (sourceSigma D d))
    (hgap : caseISourceOrderCoefficient (a₀ + a₁ + a₂) D d ≤ 1 - ρ) :
    x₀ + x₁ + x₂ ≤ (1 - ρ) * B := by
  calc
    x₀ + x₁ + x₂ ≤ (a₀ + a₁ + a₂) *
        caseI1423RemainderUnit B D (sourceSigma D d) := by linarith
    _ = caseISourceOrderCoefficient (a₀ + a₁ + a₂) D d * B := by
      unfold caseI1423RemainderUnit caseISourceOrderCoefficient
      ring
    _ ≤ (1 - ρ) * B := mul_le_mul_of_nonneg_right hgap hB

end MathlibNt.SieveTheory
