import MathlibNt.AnalyticNumberTheory.LargeSieve.LandauSiegelToLowSWSource
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Canonical smoothing data for the raw Landau--Siegel Standard-BV endpoint

This module constructs a fixed nonnegative smooth bump supported in `[1/2, 2]`,
normalizes it for the multiplicative measure `dx/x`, and removes all smoothing
data from the final raw-Landau--Siegel-to-Standard-BV headline.
-/

open Set Function Filter Complex Real MeasureTheory Metric

namespace AnalyticNumberTheory.LargeSieve

noncomputable section

/-- A concrete smooth bump centered at `5/4`, with outer radius `3/4`. -/
def standardBVCanonicalBaseBump : ContDiffBump (5 / 4 : ℝ) :=
  ⟨1 / 4, 3 / 4, by norm_num, by norm_num⟩

/-- The base bump multiplied by a globally continuous version of `1/x`.
On the support of the bump this is exactly `standardBVCanonicalBaseBump x / x`. -/
def standardBVCanonicalWeight (x : ℝ) : ℝ :=
  standardBVCanonicalBaseBump x / max x (1 / 2)

/-- The finite, strictly positive normalizing denominator. -/
def standardBVCanonicalWeightMass : ℝ :=
  ∫ x : ℝ, standardBVCanonicalWeight x

theorem standardBVCanonicalWeight_continuous : Continuous standardBVCanonicalWeight := by
  apply standardBVCanonicalBaseBump.continuous.div
  · fun_prop
  · intro x
    have h : 0 < max x (1 / 2) :=
      lt_of_lt_of_le (by norm_num) (le_max_right x (1 / 2))
    exact h.ne'

theorem standardBVCanonicalWeight_hasCompactSupport :
    HasCompactSupport standardBVCanonicalWeight := by
  exact standardBVCanonicalBaseBump.hasCompactSupport.mul_right

theorem standardBVCanonicalWeight_integrable :
    Integrable standardBVCanonicalWeight :=
  standardBVCanonicalWeight_continuous.integrable_of_hasCompactSupport
    standardBVCanonicalWeight_hasCompactSupport

theorem standardBVCanonicalWeight_nonneg : 0 ≤ standardBVCanonicalWeight := by
  intro x
  exact div_nonneg standardBVCanonicalBaseBump.nonneg (by positivity)

private lemma standardBVCanonicalWeight_at_center :
    standardBVCanonicalWeight (5 / 4) ≠ 0 := by
  have hone : standardBVCanonicalBaseBump (5 / 4) = 1 :=
    standardBVCanonicalBaseBump.one_of_mem_closedBall
      (mem_closedBall_self standardBVCanonicalBaseBump.rIn_pos.le)
  rw [standardBVCanonicalWeight, hone]
  norm_num

/-- The normalization denominator is positive (and hence nonzero). -/
theorem standardBVCanonicalWeightMass_pos : 0 < standardBVCanonicalWeightMass := by
  exact standardBVCanonicalWeight_continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    standardBVCanonicalWeight_hasCompactSupport standardBVCanonicalWeight_nonneg
    standardBVCanonicalWeight_at_center

/-- The canonical smoothing function, normalized for `dx/x`. -/
def standardBVCanonicalSmoothing (x : ℝ) : ℝ :=
  standardBVCanonicalBaseBump x / standardBVCanonicalWeightMass

/-- The canonical smoothing function is (in fact infinitely) smooth, hence `C¹`. -/
theorem standardBVCanonicalSmoothing_contDiff :
    ContDiff ℝ 1 standardBVCanonicalSmoothing := by
  exact standardBVCanonicalBaseBump.contDiff.div_const standardBVCanonicalWeightMass

/-- The canonical smoothing function is globally nonnegative. -/
theorem standardBVCanonicalSmoothing_nonneg_all (x : ℝ) :
    0 ≤ standardBVCanonicalSmoothing x := by
  exact div_nonneg standardBVCanonicalBaseBump.nonneg
    standardBVCanonicalWeightMass_pos.le

/-- The positive-axis form consumed by the existing low Siegel--Walfisz source. -/
theorem standardBVCanonicalSmoothing_nonneg (x : ℝ) (_hx : 0 < x) :
    0 ≤ standardBVCanonicalSmoothing x :=
  standardBVCanonicalSmoothing_nonneg_all x

private theorem standardBVCanonicalBaseBump_support :
    support standardBVCanonicalBaseBump ⊆ Icc (1 / 2) 2 := by
  rw [standardBVCanonicalBaseBump.support_eq, Real.ball_eq_Ioo]
  intro x hx
  norm_num [standardBVCanonicalBaseBump] at hx ⊢
  exact ⟨hx.1.le, hx.2.le⟩

/-- The canonical smoothing function is supported in `[1/2, 2]`. -/
theorem standardBVCanonicalSmoothing_support :
    support standardBVCanonicalSmoothing ⊆ Icc (1 / 2) 2 := by
  intro x hx
  apply standardBVCanonicalBaseBump_support
  exact fun hzero => hx (by simp [standardBVCanonicalSmoothing, hzero])

private lemma standardBVCanonicalWeight_eq_div (x : ℝ) (_hx : x ∈ Ioi (0 : ℝ)) :
    standardBVCanonicalWeight x = standardBVCanonicalBaseBump x / x := by
  by_cases hs : x ∈ support standardBVCanonicalBaseBump
  · rw [standardBVCanonicalWeight,
      max_eq_left (standardBVCanonicalBaseBump_support hs).1]
  · simp [standardBVCanonicalWeight, notMem_support.mp hs]

private lemma standardBVCanonicalWeight_zero_of_nonpos {x : ℝ}
    (hx : x ∉ Ioi (0 : ℝ)) : standardBVCanonicalWeight x = 0 := by
  have hout : x ∉ support standardBVCanonicalBaseBump := by
    intro hs
    apply hx
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (standardBVCanonicalBaseBump_support hs).1
  simp [standardBVCanonicalWeight, notMem_support.mp hout]

/-- The canonical smoothing function has multiplicative mass one. -/
theorem standardBVCanonicalSmoothing_mass_one :
    ∫ x in Ioi (0 : ℝ), standardBVCanonicalSmoothing x / x = 1 := by
  calc
    ∫ x in Ioi (0 : ℝ), standardBVCanonicalSmoothing x / x =
        ∫ x in Ioi (0 : ℝ),
          standardBVCanonicalWeight x / standardBVCanonicalWeightMass := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          change standardBVCanonicalSmoothing x / x =
            standardBVCanonicalWeight x / standardBVCanonicalWeightMass
          rw [standardBVCanonicalWeight_eq_div x hx, standardBVCanonicalSmoothing,
            div_right_comm]
    _ = ∫ x : ℝ,
          standardBVCanonicalWeight x / standardBVCanonicalWeightMass := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          simp [standardBVCanonicalWeight_zero_of_nonpos hx]
    _ = standardBVCanonicalWeightMass / standardBVCanonicalWeightMass :=
      integral_div _ _
    _ = 1 := div_self standardBVCanonicalWeightMass_pos.ne'

/-- A raw Landau--Siegel lower bound supplies Standard Bombieri--Vinogradov with
no smoothing function, regularity, support, or mass parameters in the headline. -/
theorem standardBombieriVinogradov_of_rawLandauSiegelLowerBound_canonicalSmoothing
    (hLandauSiegel : RawLandauSiegelLowerBound) :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov :=
  standardBombieriVinogradov_of_rawLandauSiegelLowerBound hLandauSiegel
    standardBVCanonicalSmoothing_contDiff standardBVCanonicalSmoothing_nonneg
    standardBVCanonicalSmoothing_support standardBVCanonicalSmoothing_mass_one

end

end AnalyticNumberTheory.LargeSieve
