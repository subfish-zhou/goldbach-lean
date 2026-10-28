import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernel
import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelReduction

open MeasureTheory Set
open scoped Interval
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


/-- Integration over the independent cross interval. -/
theorem goldbachG12PrimeIntegral_t_eq (h : ℝ → ℝ) (r q s : ℝ)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    (∫ t in b..c, h r / (r * q ^ 2 * s * t)) =
      h r / (r * q ^ 2 * s) * Real.log (c / b) := by
  calc
    _ = (h r / (r * q ^ 2 * s)) * ∫ t in b..c, t⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by rw [integral_inv_of_pos hb hc]

/-- The last two variables give a product of logarithms, not a log square. -/
theorem goldbachG12PrimeIntegral_inner_eq (h : ℝ → ℝ) (r : ℝ)
    {b c q : ℝ} (hq : 0 < q) (hqb : q ≤ b) (hc : 0 < c) :
    (∫ s in q..b, ∫ t in b..c, h r / (r * q ^ 2 * s * t)) =
      (h r / (r * q ^ 2)) * Real.log (c / b) * Real.log (b / q) := by
  have hb := hq.trans_le hqb
  calc
    _ = ((h r / (r * q ^ 2)) * Real.log (c / b)) * ∫ s in q..b, s⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [goldbachG12PrimeIntegral_t_eq h r q s hb hc]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by rw [integral_inv_of_pos hq hb]

/-- Primitive for the remaining inner variable. -/
theorem goldbachG12PrimeIntegral_qPrimitive_deriv {b q : ℝ}
    (hb : 0 < b) (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => (1 - Real.log (b / x)) / x)
      (Real.log (b / q) / q ^ 2) q := by
  apply (((goldbach_log_ratio_deriv hb hq).const_sub 1).div
    (hasDerivAt_id q) hq.ne').congr_deriv
  dsimp
  field_simp
  ring

theorem goldbachG12PrimeIntegral_qIntegral {b r : ℝ} (hr : 0 < r) (hrb : r ≤ b) :
    (∫ q in r..b, Real.log (b / q) / q ^ 2) =
      1 / b + (Real.log (b / r) - 1) / r := by
  have hb := hr.trans_le hrb
  have hc : ContinuousOn (fun q : ℝ => Real.log (b / q) / q ^ 2) (Icc r b) := by
    apply ContinuousOn.div
      ((continuousOn_const.div continuousOn_id
        (fun q hq => (hr.trans_le hq.1).ne')).log
          (fun q hq => div_ne_zero hb.ne' (hr.trans_le hq.1).ne'))
      (continuousOn_id.pow 2)
    intro q hq
    exact pow_ne_zero 2 (hr.trans_le hq.1).ne'
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun q hq => goldbachG12PrimeIntegral_qPrimitive_deriv hb
      (hr.trans_le (by rwa [uIcc_of_le hrb] at hq : q ∈ Icc r b).1))
    (hc.intervalIntegrable_of_Icc hrb)
  rw [he, div_self hb.ne', Real.log_one]
  ring

/-- Exact reduction of the original cross integral. Continuity is not needed for the identity. -/
theorem goldbachG12PrimeIntegral_eq_single (h : ℝ → ℝ) :
    goldbachG12PrimeIntegral h = Real.log ((3 / 11 : ℝ) / (4 / 33)) *
      ∫ r in (4 / 53 : ℝ)..(4 / 33), h r / r *
        (1 / (4 / 33 : ℝ) + (Real.log ((4 / 33 : ℝ) / r) - 1) / r) := by
  unfold goldbachG12PrimeIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 4 / 33)] at hr
  calc
    _ = (Real.log ((3 / 11 : ℝ) / (4 / 33)) * (h r / r)) *
        ∫ q in r..(4 / 33 : ℝ), Real.log ((4 / 33 : ℝ) / q) / q ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le hr.2] at hq
      dsimp only
      rw [goldbachG12PrimeIntegral_inner_eq h r (by linarith [hr.1, hq.1]) hq.2
        (by norm_num : (0 : ℝ) < 3 / 11)]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by
      rw [goldbachG12PrimeIntegral_qIntegral (by linarith [hr.1]) hr.2]
      ring


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
