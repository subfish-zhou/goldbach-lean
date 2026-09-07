import MathlibNt.SieveTheory.LiLiuGoldbachG67G67Specialization
import MathlibNt.SieveTheory.LiLiuGoldbachG67SumWeightProperties

open Set MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section
namespace G67SumCoordinate

/-- Split a compact continuous integral at an interior point. -/
theorem split_integral {l m r : ℝ} {f : ℝ → ℝ}
    (hlm : l ≤ m) (hmr : m ≤ r) (hf : ContinuousOn f (Icc l r)) :
    (∫ s in l..r, f s) = (∫ s in l..m, f s) + (∫ s in m..r, f s) := by
  apply Eq.symm
  apply intervalIntegral.integral_add_adjacent_intervals
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlm]
    exact hf.mono (Icc_subset_Icc le_rfl hmr)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hmr]
    exact hf.mono (Icc_subset_Icc hlm le_rfl)

/-- Continuity of the actual square density on its full sum interval. -/
theorem square_density_continuousOn : ContinuousOn
    (fun s => profile s * weight (4/53) (4/33) (4/53) (4/33) s)
    (Icc ((4/53 : ℝ)+(4/53 : ℝ)) ((4/33 : ℝ)+(4/33 : ℝ))) := by
  exact (profile_continuousOn.mono (Icc_subset_Icc le_rfl (by norm_num))).mul
    (weight_continuousOn (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- Continuity of the actual rectangular density on its full sum interval. -/
theorem rectangle_density_continuousOn : ContinuousOn
    (fun s => profile s * weight (4/53) (4/33) (4/33) (3/11) s)
    (Icc ((4/53 : ℝ)+(4/33 : ℝ)) ((4/33 : ℝ)+(3/11 : ℝ))) := by
  exact (profile_continuousOn.mono (Icc_subset_Icc (by norm_num) le_rfl)).mul
    (weight_continuousOn (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- Exact removal of the zero tail, not an inequality or a numerical approximation. -/
theorem rectangle_integral_truncate :
    (∫ s in ((4/53 : ℝ)+(4/33 : ℝ))..((4/33 : ℝ)+(3/11 : ℝ)),
      profile s * weight (4/53) (4/33) (4/33) (3/11) s) =
    (∫ s in ((4/53 : ℝ)+(4/33 : ℝ))..((1/2 : ℝ)-2*(4/53 : ℝ)),
      profile s * weight (4/53) (4/33) (4/33) (3/11) s) := by
  rw [split_integral (m := (1/2 : ℝ)-2*(4/53 : ℝ)) (by norm_num) (by norm_num)
    rectangle_density_continuousOn]
  have hz : (∫ s in ((1/2 : ℝ)-2*(4/53 : ℝ))..((4/33 : ℝ)+(3/11 : ℝ)),
      profile s * weight (4/53) (4/33) (4/33) (3/11) s) = 0 := by
    calc
      _ = ∫ s in ((1/2 : ℝ)-2*(4/53 : ℝ))..((4/33 : ℝ)+(3/11 : ℝ)), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by norm_num)] at hs
        change profile s * weight (4/53) (4/33) (4/33) (3/11) s = 0
        rw [profile_zero hs.1 hs.2, zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  rw [hz, add_zero]

/-- The exact one-dimensional auxiliary constant with its identically zero tail removed. -/
def truncatedIntegral : ℝ :=
  (1/2 : ℝ) * (∫ s in ((4/53 : ℝ)+(4/53 : ℝ))..((4/33 : ℝ)+(4/33 : ℝ)),
    profile s * weight (4/53) (4/33) (4/53) (4/33) s) +
  (∫ s in ((4/53 : ℝ)+(4/33 : ℝ))..((1/2 : ℝ)-2*(4/53 : ℝ)),
    profile s * weight (4/53) (4/33) (4/33) (3/11) s)

/-- Unconditional exact equality to the imported original elementary integral. -/
theorem elementaryIntegral_eq_truncated :
    G67ElementaryIntegral.elementaryIntegral = truncatedIntegral := by
  rw [elementaryIntegral_eq_oneDimensional]
  unfold oneDimensionalIntegral truncatedIntegral
  rw [rectangle_integral_truncate]

/-- Actual C67 consumer after exact tail removal. -/
theorem actual_constant_lower_truncated :
    4 * truncatedIntegral ≤ goldbachG67IntegralConstant := by
  rw [← elementaryIntegral_eq_truncated]
  exact G67ElementaryIntegral.actual_constant_lower

end G67SumCoordinate
