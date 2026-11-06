import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The weight and substitution in Wu (2004), Lemma 6.1 (6.3)

Source: author TeX lines 2594--2608. These identities use only the
nonvanishing denominators; no regularity of the gain is assumed.
-/

namespace Wu2008DoubleSieve

open Set MeasureTheory Real
open scoped Interval

noncomputable def firstFeedbackWeightedKernel (c u : ℝ) : ℝ := c / (u * (c - u))



theorem firstFeedbackWeightedKernel_integral {A B c : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hBc : B < c) :
    (∫ u in A..B, firstFeedbackWeightedKernel c u) =
      log (B * (c - A) / (A * (c - B))) := by
  have hB := hA.trans_le hAB
  have hcB : 0 < c - B := sub_pos.mpr hBc
  have hcA : 0 < c - A := by linarith
  have hi : IntervalIntegrable (fun u : ℝ => u⁻¹) volume A B := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    rw [uIcc_of_le hAB]
    intro u hu
    exact ne_of_gt (hA.trans_le hu.1)
  have hj : IntervalIntegrable (fun u : ℝ => (c - u)⁻¹) volume A B := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_const.sub continuousOn_id).inv₀
    rw [uIcc_of_le hAB]
    intro u hu
    exact ne_of_gt (sub_pos.mpr (hu.2.trans_lt hBc))
  calc
    _ = ∫ u in A..B, u⁻¹ + (c - u)⁻¹ := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hAB]
      intro u hu
      have hu0 := ne_of_gt (hA.trans_le hu.1)
      have hcu0 := ne_of_gt (sub_pos.mpr (hu.2.trans_lt hBc))
      dsimp [firstFeedbackWeightedKernel]
      field_simp
      ring
    _ = log (B / A) + log ((c - A) / (c - B)) := by
      rw [intervalIntegral.integral_add hi hj,
        intervalIntegral.integral_comp_sub_left (fun u : ℝ => u⁻¹) c,
        integral_inv_of_pos hA hB, integral_inv_of_pos hcB hcA]
    _ = _ := by
      rw [← log_mul (ne_of_gt (div_pos hB hA)) (ne_of_gt (div_pos hcA hcB))]
      congr 1
      field_simp





end Wu2008DoubleSieve
