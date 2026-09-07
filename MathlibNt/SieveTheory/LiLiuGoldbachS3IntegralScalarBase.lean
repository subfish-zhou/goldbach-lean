import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarEndpoints
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Set MeasureTheory
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Exact base-kernel integration on the whole positive interval. -/
theorem goldbachS3_scalar_base_integral {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b < c) :
    (∫ s in a..b, 1 / (s * (c-s))) =
      ((Real.log b - Real.log (c-b)) -
        (Real.log a - Real.log (c-a))) / c := by
  have hc : c ≠ 0 := ne_of_gt (ha.trans_le (hab.trans hbc.le))
  have hd : ∀ s ∈ uIcc a b,
      HasDerivAt (fun s : ℝ => (Real.log s - Real.log (c-s))/c)
        (1/(s*(c-s))) s := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hs0 : s ≠ 0 := ne_of_gt (ha.trans_le hs.1)
    have hcs : c-s ≠ 0 := ne_of_gt (sub_pos.mpr (hs.2.trans_lt hbc))
    convert ((Real.hasDerivAt_log hs0).sub
      ((Real.hasDerivAt_log hcs).comp s ((hasDerivAt_id s).const_sub c))).div_const c using 1 <;>
      first | rfl | (field_simp [hs0, hcs, hc]; ring)
  have hi : IntervalIntegrable (fun s : ℝ => 1/(s*(c-s))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    apply continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    intro s hs
    exact mul_ne_zero (ne_of_gt (ha.trans_le hs.1))
      (ne_of_gt (sub_pos.mpr (hs.2.trans_lt hbc)))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  convert h using 1
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig