import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem g11_log_ratio_deriv {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (b / y)) (-1 / x) x := by
  have hd := ((hasDerivAt_const x b).div (hasDerivAt_id x) hx.ne').log
    (div_ne_zero hb.ne' hx.ne')
  apply hd.congr_deriv
  dsimp
  field_simp
  ring

theorem goldbachG11PrimeIntegral_logTriangle {b q : ℝ} (hq : 0 < q) (hqb : q ≤ b) :
    (∫ s in q..b, ∫ t in s..b, 1 / (s * t)) = Real.log (b / q) ^ 2 / 2 := by
  have hb : 0 < b := hq.trans_le hqb
  have hc : ContinuousOn (fun s : ℝ => Real.log (b / s) / s) (Icc q b) := by
    exact (continuousOn_const.div continuousOn_id (fun x hx => (hq.trans_le hx.1).ne')).log
      (fun x hx => div_ne_zero hb.ne' (hq.trans_le hx.1).ne') |>.div
        continuousOn_id (fun x hx => (hq.trans_le hx.1).ne')
  have hd (x : ℝ) (hx : x ∈ Icc q b) :
      HasDerivAt (fun s : ℝ => -(Real.log (b / s) ^ 2) / 2)
        (Real.log (b / x) / x) x := by
    have hx0 := hq.trans_le hx.1
    apply (((g11_log_ratio_deriv hb hx0).pow 2).neg.div_const 2).congr_deriv
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by rwa [uIcc_of_le hqb] at hx))
    (hc.intervalIntegrable_of_Icc hqb)
  calc
    _ = ∫ s in q..b, Real.log (b / s) / s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hqb] at hs
      have hs0 := hq.trans_le hs.1
      calc
        _ = (1 / s) * ∫ t in s..b, t⁻¹ := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t _
          simp only [one_div, mul_inv]
        _ = _ := by rw [integral_inv_of_pos hs0 hb]; ring
    _ = _ := by
      rw [he, div_self hb.ne', Real.log_one]
      ring

theorem goldbachG11PrimeIntegral_inner_eq {b q r : ℝ} (h : ℝ → ℝ)
    (hq : 0 < q) (hqb : q ≤ b) :
    (∫ s in q..b, ∫ t in s..b, h r / (r * q ^ 2 * s * t)) =
      (h r / (r * q ^ 2)) * (Real.log (b / q) ^ 2 / 2) := by
  calc
    _ = (h r / (r * q ^ 2)) * ∫ s in q..b, ∫ t in s..b, 1 / (s * t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by rw [goldbachG11PrimeIntegral_logTriangle hq hqb]

theorem goldbachG11PrimeIntegral_eq_double (h : ℝ → ℝ) :
    goldbachG11PrimeIntegral h =
      ∫ r in (4 / 53 : ℝ)..(4 / 33), ∫ q in r..(4 / 33),
        h r / (r * q ^ 2) * (Real.log ((4 / 33 : ℝ) / q) ^ 2 / 2) := by
  unfold goldbachG11PrimeIntegral
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 4 / 33)] at hr
  apply intervalIntegral.integral_congr
  intro q hq
  rw [uIcc_of_le hr.2] at hq
  exact goldbachG11PrimeIntegral_inner_eq h (by linarith [hr.1, hq.1]) hq.2

theorem goldbachG11PrimeIntegral_qPrimitive_deriv {b q : ℝ}
    (hb : 0 < b) (hq : 0 < q) :
    HasDerivAt (fun x : ℝ =>
      -(Real.log (b / x) ^ 2 - 2 * Real.log (b / x) + 2) / x)
      (Real.log (b / q) ^ 2 / q ^ 2) q := by
  have hd := g11_log_ratio_deriv hb hq
  apply ((((hd.pow 2).sub (hd.const_mul 2)).add_const 2).neg.div
    (hasDerivAt_id q) hq.ne').congr_deriv
  dsimp
  field_simp
  ring

theorem goldbachG11PrimeIntegral_qIntegral {b r : ℝ} (hr : 0 < r) (hrb : r ≤ b) :
    (∫ q in r..b, Real.log (b / q) ^ 2 / q ^ 2) =
      (Real.log (b / r) ^ 2 - 2 * Real.log (b / r) + 2) / r - 2 / b := by
  have hb := hr.trans_le hrb
  have hc : ContinuousOn (fun q : ℝ => Real.log (b / q) ^ 2 / q ^ 2) (Icc r b) := by
    apply ContinuousOn.div
      (((continuousOn_const.div continuousOn_id
        (fun q hq => (hr.trans_le hq.1).ne')).log
          (fun q hq => div_ne_zero hb.ne' (hr.trans_le hq.1).ne')).pow 2)
      (continuousOn_id.pow 2)
    intro q hq
    exact pow_ne_zero 2 (hr.trans_le hq.1).ne'
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun q hq => goldbachG11PrimeIntegral_qPrimitive_deriv hb
      (hr.trans_le (by rwa [uIcc_of_le hrb] at hq : q ∈ Icc r b).1))
    (hc.intervalIntegrable_of_Icc hrb)
  rw [he, div_self hb.ne', Real.log_one]
  ring

theorem goldbachG11PrimeIntegral_eq_single (h : ℝ → ℝ) :
    goldbachG11PrimeIntegral h =
      ∫ r in (4 / 53 : ℝ)..(4 / 33),
        h r / r *
          ((Real.log ((4 / 33 : ℝ) / r) ^ 2 -
            2 * Real.log ((4 / 33 : ℝ) / r) + 2) / r - 2 / (4 / 33 : ℝ)) / 2 := by
  rw [goldbachG11PrimeIntegral_eq_double]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 4 / 33)] at hr
  calc
    _ = (h r / r / 2) * ∫ q in r..(4 / 33 : ℝ),
        Real.log ((4 / 33 : ℝ) / q) ^ 2 / q ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro q _
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by
      rw [goldbachG11PrimeIntegral_qIntegral (by linarith [hr.1]) hr.2]
      ring

theorem intervalIntegrable_goldbachG11PrimeSingleIntegrand (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33))) :
    IntervalIntegrable (fun r : ℝ => h r / r *
      ((Real.log ((4 / 33 : ℝ) / r) ^ 2 -
        2 * Real.log ((4 / 33 : ℝ) / r) + 2) / r - 2 / (4 / 33 : ℝ)) / 2)
      volume (4 / 53) (4 / 33) := by
  have hn : ∀ r ∈ Icc (4 / 53 : ℝ) (4 / 33), r ≠ 0 := by
    intro r hr
    linarith [hr.1]
  have hl : ContinuousOn (fun r : ℝ => Real.log ((4 / 33 : ℝ) / r))
      (Icc (4 / 53 : ℝ) (4 / 33)) :=
    (continuousOn_const.div continuousOn_id hn).log
      (fun r hr => div_ne_zero (by norm_num) (hn r hr))
  exact (((hh.div continuousOn_id hn).mul
    (((((hl.pow 2).sub (continuousOn_const.mul hl)).add continuousOn_const).div
      continuousOn_id hn).sub continuousOn_const)).div_const 2).intervalIntegrable_of_Icc
        (by norm_num)

theorem goldbachG11PrimeIntegral_one_eq_single :
    goldbachG11PrimeIntegral (fun _ => 1) =
      ∫ r in (4 / 53 : ℝ)..(4 / 33),
        ((Real.log ((4 / 33 : ℝ) / r) ^ 2 -
          2 * Real.log ((4 / 33 : ℝ) / r) + 2) / r - 2 / (4 / 33 : ℝ)) / (2 * r) := by
  rw [goldbachG11PrimeIntegral_eq_single]
  apply intervalIntegral.integral_congr
  intro r _
  ring

theorem goldbachG11PrimeIntegral_author_eq_single :
    goldbachG11PrimeIntegral goldbachG11AuthorWeight =
      ∫ r in (4 / 53 : ℝ)..(4 / 33),
        goldbachG11AuthorWeight r / r *
          ((Real.log ((4 / 33 : ℝ) / r) ^ 2 -
            2 * Real.log ((4 / 33 : ℝ) / r) + 2) / r - 2 / (4 / 33 : ℝ)) / 2 :=
  goldbachG11PrimeIntegral_eq_single _

theorem goldbachG11PrimeIntegral_nonneg (h : ℝ → ℝ)
    (hh : ∀ r ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h r) :
    0 ≤ goldbachG11PrimeIntegral h := by
  unfold goldbachG11PrimeIntegral
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro r hr
  apply intervalIntegral.integral_nonneg hr.2
  intro q hq
  apply intervalIntegral.integral_nonneg hq.2
  intro s hs
  apply intervalIntegral.integral_nonneg hs.2
  intro t ht
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hs0 : 0 ≤ s := by linarith [hq.1, hs.1]
  have ht0 : 0 ≤ t := hs0.trans ht.1
  exact div_nonneg (hh r hr) (mul_nonneg (mul_nonneg (mul_nonneg hr0 (sq_nonneg q)) hs0) ht0)

theorem goldbachG11PrimeIntegral_const (c : ℝ) :
    goldbachG11PrimeIntegral (fun _ => c) = c * goldbachG11PrimeIntegral (fun _ => 1) := by
  rw [goldbachG11PrimeIntegral_eq_single, goldbachG11PrimeIntegral_eq_single,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  ring

theorem goldbachG11PrimeIntegral_author_split :
    goldbachG11PrimeIntegral goldbachG11AuthorWeight =
      (36 / 5 : ℝ) * (∫ r in (4 / 53 : ℝ)..(1 / 10),
        ((Real.log ((4 / 33 : ℝ) / r) ^ 2 -
          2 * Real.log ((4 / 33 : ℝ) / r) + 2) / r - 2 / (4 / 33 : ℝ)) /
            (2 * r * (1 - r))) +
      8 * (∫ r in (1 / 10 : ℝ)..(4 / 33),
        ((Real.log ((4 / 33 : ℝ) / r) ^ 2 -
          2 * Real.log ((4 / 33 : ℝ) / r) + 2) / r - 2 / (4 / 33 : ℝ)) / (2 * r)) := by
  let F : ℝ → ℝ := fun r =>
    goldbachG11AuthorWeight r / r *
      ((Real.log ((4 / 33 : ℝ) / r) ^ 2 -
        2 * Real.log ((4 / 33 : ℝ) / r) + 2) / r - 2 / (4 / 33 : ℝ)) / 2
  have hF : IntervalIntegrable F volume (4 / 53) (4 / 33) :=
    intervalIntegrable_goldbachG11PrimeSingleIntegrand _ continuousOn_goldbachG11AuthorWeight
  have hc : (1 / 10 : ℝ) ∈ uIcc (4 / 53 : ℝ) (4 / 33) := by
    rw [uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 4 / 33)]
    constructor <;> norm_num
  rw [goldbachG11PrimeIntegral_author_eq_single]
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