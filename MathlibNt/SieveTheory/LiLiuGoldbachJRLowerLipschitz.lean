import MathlibNt.SieveTheory.LiLiuPrereqWFCoordinateShift

/-! Actual JR lower function: global real-domain Lipschitz and endpoint control. -/

noncomputable section

open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.LiLiuPrereqWF.CoordinateShift

namespace MathlibNt.SieveTheory.LiLiuGoldbachJRLowerLipschitz

/-- The zero extension below two makes the actual lower function globally monotone. -/
theorem lower_monotone : Monotone jr1965f := by
  intro x y hxy
  by_cases hy : y ≤ 2
  · rw [jr1965f_initial (hxy.trans hy), jr1965f_initial hy]
  · have hy0 : 0 < y := by linarith
    by_cases hx : x ≤ 2
    · rw [jr1965f_initial hx]
      exact jr1965f_nonneg hy0
    · exact monotoneOn_jr1965f (by change 0 < x; linarith)
        (by change 0 < y; exact hy0) hxy

/-- Ordered global increment bound, including intervals crossing two. -/
theorem lower_sub_le_half_constant_mul {x y : ℝ} (hxy : x ≤ y) :
    jr1965f y - jr1965f x ≤ jr1965DelayConstant / 2 * (y - x) := by
  have hc : 0 ≤ jr1965DelayConstant / 2 := div_nonneg delayConstant_pos.le (by norm_num)
  by_cases hy : y ≤ 2
  · rw [jr1965f_initial (hxy.trans hy), jr1965f_initial hy, sub_self]
    exact mul_nonneg hc (sub_nonneg.mpr hxy)
  · have hy2 : 2 ≤ y := le_of_lt (lt_of_not_ge hy)
    by_cases hx : x ≤ 2
    · have h := lower_sub_le_relative_length (s := 2) (by norm_num) hy2
      rw [jr1965f_initial (u := 2) (by norm_num), sub_zero] at h
      rw [jr1965f_initial hx, sub_zero]
      exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hc)
    · have hx2 : 2 ≤ x := le_of_lt (lt_of_not_ge hx)
      have hdiv : jr1965DelayConstant / x ≤ jr1965DelayConstant / 2 :=
        div_le_div_of_nonneg_left delayConstant_pos.le (by norm_num) hx2
      exact (lower_sub_le_relative_length hx2 hxy).trans
        (mul_le_mul_of_nonneg_right hdiv (sub_nonneg.mpr hxy))

/-- Global Lipschitz estimate: neither input is assumed positive. -/
theorem lower_abs_sub_le (x y : ℝ) :
    |jr1965f x - jr1965f y| ≤ jr1965DelayConstant / 2 * |x - y| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (lower_monotone hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa only [neg_sub] using lower_sub_le_half_constant_mul hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr (lower_monotone hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact lower_sub_le_half_constant_mul hyx

/-- One-sided transport form for downstream nonnegative-counting branches. -/
theorem lower_le_add_abs (x y : ℝ) :
    jr1965f y ≤ jr1965f x + jr1965DelayConstant / 2 * |x - y| := by
  have h := lower_abs_sub_le x y
  have hneg := neg_le_abs (jr1965f x - jr1965f y)
  linarith

/-- If the source is at or below two, the target may lie on either side of two. -/
theorem lower_le_near_two {x y η : ℝ} (hx : x ≤ 2)
    (hclose : |x - y| < η) :
    jr1965f y ≤ jr1965DelayConstant / 2 * η := by
  have h := lower_le_add_abs x y
  rw [jr1965f_initial hx, zero_add] at h
  have hc : 0 < jr1965DelayConstant / 2 := div_pos delayConstant_pos (by norm_num)
  exact h.trans (mul_lt_mul_of_pos_left hclose hc).le

end MathlibNt.SieveTheory.LiLiuGoldbachJRLowerLipschitz
