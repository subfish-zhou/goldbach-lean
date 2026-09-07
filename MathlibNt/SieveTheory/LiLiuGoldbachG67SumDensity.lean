import MathlibNt.SieveTheory.LiLiuGoldbachG67SumGeometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Set MeasureTheory
open scoped Interval
noncomputable section
namespace G67SumCoordinate

/-- Exact integration of the reciprocal density along a positive sum fiber. -/
theorem integral_fiber_density {L U s : ℝ} (hL : 0 < L) (hLU : L ≤ U)
    (hU : U < s) :
    (∫ u in L..U, 1 / (u * (s-u))) =
      Real.log (U*(s-L)/(L*(s-U))) / s := by
  have hs : s ≠ 0 := ne_of_gt (lt_trans (lt_of_lt_of_le hL hLU) hU)
  have hUp : 0 < U := lt_of_lt_of_le hL hLU
  have hsL : 0 < s-L := by linarith
  have hsU : 0 < s-U := sub_pos.mpr hU
  have hint : IntervalIntegrable (fun u => 1 / (u*(s-u))) volume L U := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn
    intro u hu
    rw [uIcc_of_le hLU] at hu
    change u * (s-u) ≠ 0
    exact (mul_pos (lt_of_lt_of_le hL hu.1) (by linarith [hu.2])).ne'
  have hderiv : ∀ u ∈ uIcc L U,
      HasDerivAt (fun u : ℝ => (Real.log u - Real.log (s-u))/s)
        (1/(u*(s-u))) u := by
    intro u hu
    rw [uIcc_of_le hLU] at hu
    have hu0 : u ≠ 0 := (lt_of_lt_of_le hL hu.1).ne'
    have hsu : s-u ≠ 0 := (show 0 < s-u by linarith [hu.2]).ne'
    convert (((hasDerivAt_id u).log hu0).sub
      (((hasDerivAt_const u s).sub (hasDerivAt_id u)).log hsu)).div_const s using 1 <;>
      first | rfl | (dsimp; field_simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [Real.log_div (mul_pos hUp hsL).ne' (mul_pos hL hsU).ne',
    Real.log_mul hUp.ne' hsL.ne', Real.log_mul hL.ne' hsU.ne']
  ring

/-- The closed-form fiber weight, including its zero endpoint values. -/
def weight (a b c d s : ℝ) : ℝ :=
  Real.log (upper b c s * (s-lower a d s) /
    (lower a d s * (s-upper b c s))) / s

/-- No antiderivative or fiber integral is carried as a premise. -/
theorem fiber_integral {a b c d s : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) (hs : s ∈ Icc (a+c) (b+d)) :
    (∫ u in lower a d s..upper b c s, 1/(u*(s-u))) = weight a b c d s := by
  have hb := fiber_bounds ha hc hab hcd hs
  exact integral_fiber_density hb.1 hb.2.1 (by linarith [hb.2.2])

end G67SumCoordinate
