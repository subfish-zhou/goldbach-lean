import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernel
import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelReduction

open MeasureTheory Set
open scoped Interval
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem g12_log_ratio_deriv {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (b / y)) (-1 / x) x := by
  have hd := ((hasDerivAt_const x b).div (hasDerivAt_id x) hx.ne').log
    (div_ne_zero hb.ne' hx.ne')
  apply hd.congr_deriv
  dsimp
  field_simp
  ring

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
  apply (((g12_log_ratio_deriv hb hq).const_sub 1).div
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

/-- Continuous weights give a genuinely integrable one-dimensional integrand. -/
theorem intervalIntegrable_goldbachG12PrimeSingleIntegrand (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33))) :
    IntervalIntegrable (fun r : ℝ => h r / r *
      (1 / (4 / 33 : ℝ) + (Real.log ((4 / 33 : ℝ) / r) - 1) / r))
      volume (4 / 53) (4 / 33) := by
  have hn : ∀ r ∈ Icc (4 / 53 : ℝ) (4 / 33), r ≠ 0 := by
    intro r hr
    linarith [hr.1]
  have hl : ContinuousOn (fun r : ℝ => Real.log ((4 / 33 : ℝ) / r))
      (Icc (4 / 53 : ℝ) (4 / 33)) :=
    (continuousOn_const.div continuousOn_id hn).log
      (fun r hr => div_ne_zero (by norm_num) (hn r hr))
  exact ((hh.div continuousOn_id hn).mul
    (continuousOn_const.add ((hl.sub continuousOn_const).div continuousOn_id hn))).intervalIntegrable_of_Icc (by norm_num)

/-- Primitive of the constant-weight reduced kernel. -/
theorem goldbachG12PrimeIntegral_onePrimitive_deriv {b r : ℝ}
    (hb : 0 < b) (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => -Real.log (b / x) / b + (2 - Real.log (b / x)) / x)
      (1 / r * (1 / b + (Real.log (b / r) - 1) / r)) r := by
  have hd := g12_log_ratio_deriv hb hr
  apply ((hd.neg.div_const b).add ((hd.const_sub 2).div (hasDerivAt_id r) hr.ne')).congr_deriv
  dsimp
  field_simp
  ring

/-- Closed form for the constant weight on the original cross domain. -/
theorem goldbachG12PrimeIntegral_one_closed :
    goldbachG12PrimeIntegral (fun _ => 1) =
      Real.log (9 / 4 : ℝ) * ((43 / 2 : ℝ) * Real.log (53 / 33 : ℝ) - 10) := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => goldbachG12PrimeIntegral_onePrimitive_deriv
      (by norm_num : (0 : ℝ) < 4 / 33)
      (by rw [uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 4 / 33)] at hr
          linarith [hr.1]))
    (intervalIntegrable_goldbachG12PrimeSingleIntegrand (fun _ => 1) continuousOn_const)
  rw [goldbachG12PrimeIntegral_eq_single, he]
  norm_num
  ring

/-- Every literal innermost cross slice is integrable. -/
theorem goldbachG12PrimeIntegral_t_intervalIntegrable (h : ℝ → ℝ) {r q s : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hs : 0 < s) :
    IntervalIntegrable (fun t : ℝ => h r / (r * q ^ 2 * s * t))
      volume (4 / 33) (3 / 11) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  apply continuousOn_const.div (by fun_prop)
  intro t ht
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hr.ne' (pow_ne_zero 2 hq.ne')) hs.ne')
    (by linarith [ht.1])

/-- The once-integrated literal cross kernel is integrable. -/
theorem goldbachG12PrimeIntegral_s_intervalIntegrable (h : ℝ → ℝ) {r q : ℝ}
    (hq : 0 < q) (hqb : q ≤ (4 / 33 : ℝ)) :
    IntervalIntegrable (fun s : ℝ => ∫ t in (4 / 33 : ℝ)..(3 / 11),
      h r / (r * q ^ 2 * s * t)) volume q (4 / 33) := by
  apply ContinuousOn.intervalIntegrable_of_Icc hqb
  have hn : ∀ s ∈ Icc q (4 / 33 : ℝ), s ≠ 0 :=
    fun s hs => (hq.trans_le hs.1).ne'
  apply ((continuousOn_const.div continuousOn_id hn).mul continuousOn_const).congr
  intro s _
  dsimp only
  rw [goldbachG12PrimeIntegral_t_eq h r q s (by norm_num) (by norm_num)]
  show h r / (r * q ^ 2 * s) * Real.log ((3 / 11 : ℝ) / (4 / 33)) =
    (h r / (r * q ^ 2)) / s * Real.log ((3 / 11 : ℝ) / (4 / 33))
  ring

/-- The twice-integrated literal cross kernel is integrable. -/
theorem goldbachG12PrimeIntegral_q_intervalIntegrable (h : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) (hrb : r ≤ (4 / 33 : ℝ)) :
    IntervalIntegrable (fun q : ℝ => ∫ s in q..(4 / 33 : ℝ),
      ∫ t in (4 / 33 : ℝ)..(3 / 11), h r / (r * q ^ 2 * s * t))
      volume r (4 / 33) := by
  have hn : ∀ q ∈ Icc r (4 / 33 : ℝ), q ≠ 0 :=
    fun q hq => (hr.trans_le hq.1).ne'
  have hl : ContinuousOn (fun q : ℝ => Real.log ((4 / 33 : ℝ) / q))
      (Icc r (4 / 33 : ℝ)) :=
    (continuousOn_const.div continuousOn_id hn).log
      (fun q hq => div_ne_zero (by norm_num) (hn q hq))
  apply ContinuousOn.intervalIntegrable_of_Icc hrb
  apply (((continuousOn_const.div (continuousOn_id.pow 2)
    (fun q hq => pow_ne_zero 2 (hn q hq))).mul continuousOn_const).mul hl).congr
  intro q hq
  dsimp only
  rw [goldbachG12PrimeIntegral_inner_eq h r (hr.trans_le hq.1) hq.2 (by norm_num)]
  show h r / (r * q ^ 2) * Real.log ((3 / 11 : ℝ) / (4 / 33)) *
      Real.log ((4 / 33 : ℝ) / q) =
    (h r / r) / q ^ 2 * Real.log ((3 / 11 : ℝ) / (4 / 33)) *
      Real.log ((4 / 33 : ℝ) / q)
  ring

/-- The outer literal slice has the same pointwise reduction. -/
theorem goldbachG12PrimeIntegral_rSlice_eq (h : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) (hrb : r ≤ (4 / 33 : ℝ)) :
    (∫ q in r..(4 / 33 : ℝ), ∫ s in q..(4 / 33 : ℝ),
      ∫ t in (4 / 33 : ℝ)..(3 / 11), h r / (r * q ^ 2 * s * t)) =
    Real.log ((3 / 11 : ℝ) / (4 / 33)) * (h r / r *
      (1 / (4 / 33 : ℝ) + (Real.log ((4 / 33 : ℝ) / r) - 1) / r)) := by
  calc
    _ = (Real.log ((3 / 11 : ℝ) / (4 / 33)) * (h r / r)) *
        ∫ q in r..(4 / 33 : ℝ), Real.log ((4 / 33 : ℝ) / q) / q ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le hrb] at hq
      dsimp only
      rw [goldbachG12PrimeIntegral_inner_eq h r (hr.trans_le hq.1) hq.2 (by norm_num)]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by rw [goldbachG12PrimeIntegral_qIntegral hr hrb]; ring

/-- Continuous weights also make the original outer literal slice integrable. -/
theorem goldbachG12PrimeIntegral_r_intervalIntegrable (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33))) :
    IntervalIntegrable (fun r : ℝ => ∫ q in r..(4 / 33 : ℝ),
      ∫ s in q..(4 / 33 : ℝ), ∫ t in (4 / 33 : ℝ)..(3 / 11),
        h r / (r * q ^ 2 * s * t)) volume (4 / 53) (4 / 33) := by
  apply ((intervalIntegrable_goldbachG12PrimeSingleIntegrand h hh).const_mul
    (Real.log ((3 / 11 : ℝ) / (4 / 33)))).congr
  intro r hr
  have hr := uIoc_subset_uIcc hr
  rw [uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 4 / 33)] at hr
  exact (goldbachG12PrimeIntegral_rSlice_eq h (by linarith [hr.1]) hr.2).symm

/-- Exact piecewise one-dimensional formula for the author's weight. -/
theorem goldbachG12PrimeIntegral_author_split :
    goldbachG12PrimeIntegral goldbachG11AuthorWeight = Real.log (9 / 4 : ℝ) *
      ((36 / 5 : ℝ) * (∫ r in (4 / 53 : ℝ)..(1 / 10),
        (1 / (4 / 33 : ℝ) + (Real.log ((4 / 33 : ℝ) / r) - 1) / r) /
          (r * (1 - r))) +
      8 * (∫ r in (1 / 10 : ℝ)..(4 / 33),
        (1 / (4 / 33 : ℝ) + (Real.log ((4 / 33 : ℝ) / r) - 1) / r) / r)) := by
  let F : ℝ → ℝ := fun r => goldbachG11AuthorWeight r / r *
    (1 / (4 / 33 : ℝ) + (Real.log ((4 / 33 : ℝ) / r) - 1) / r)
  have hF : IntervalIntegrable F volume (4 / 53) (4 / 33) :=
    intervalIntegrable_goldbachG12PrimeSingleIntegrand _ continuousOn_goldbachG11AuthorWeight
  have hc : (1 / 10 : ℝ) ∈ uIcc (4 / 53 : ℝ) (4 / 33) := by
    rw [uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 4 / 33)]
    constructor <;> norm_num
  rw [goldbachG12PrimeIntegral_eq_single]
  rw [show (3 / 11 : ℝ) / (4 / 33) = 9 / 4 by norm_num]
  congr 1
  change (∫ r in (4 / 53 : ℝ)..(4 / 33), F r) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hF.mono_set (uIcc_subset_uIcc left_mem_uIcc hc))
    (hF.mono_set (uIcc_subset_uIcc hc right_mem_uIcc))]
  congr 1
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 1 / 10)] at hr
    dsimp [F]
    rw [goldbachG11AuthorWeight_eq_low hr.2]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 4 / 33)] at hr
    dsimp [F]
    rw [goldbachG11AuthorWeight_eq_high hr.1]
    ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
