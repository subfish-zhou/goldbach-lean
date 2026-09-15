import MathlibNt.AnalyticNumberTheory.LargeSieve.TruncatedPerronKernel
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimitivePerron
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

noncomputable section

open MeasureTheory
open scoped Interval

namespace AnalyticNumberTheory.LargeSieve

/-- The exponentially damped Perron step kernel. -/
def dampedArctanPerronKernel (ε x : ℝ) : ℝ :=
  1 / 2 + Real.arctan (x / ε) / Real.pi

/-- Exact exponentially damped sine-integral formula at positive frequency. -/
private theorem integral_exp_neg_mul_truncatedPerronIntegrand_of_pos
    {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-ε * t) * truncatedPerronIntegrand x t =
      Real.arctan (x / ε) := by
  let g : ℝ → ℝ := fun u => Real.exp (-(ε / x) * u) * Real.sinc u
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi g 0 hx
  have hbase :=
    MathlibNt.SieveTheory.LiuWeight.liuPanIntegralIoiExpNegMulSinc_eq_arctan_inv
      (ε / x) (div_pos hε hx)
  rw [mul_zero] at hscale
  calc
    (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-ε * t) * truncatedPerronIntegrand x t) =
        ∫ t : ℝ in Set.Ioi 0, x * g (x * t) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [truncatedPerronIntegrand_eq_mul_sinc]
          dsimp only [g]
          have hexpArg : -(ε / x) * (x * t) = -ε * t := by
            field_simp [hx.ne']
          rw [hexpArg]
          ring
    _ = x * ∫ t : ℝ in Set.Ioi 0, g (x * t) := by
          rw [MeasureTheory.integral_const_mul]
    _ = x * (x⁻¹ * ∫ u : ℝ in Set.Ioi 0, g u) := by
          rw [hscale]
          rfl
    _ = ∫ u : ℝ in Set.Ioi 0, g u := by field_simp [hx.ne']
    _ = Real.arctan ((ε / x)⁻¹) := hbase
    _ = Real.arctan (x / ε) := by
          congr 1
          field_simp [hε.ne', hx.ne']

/-- The damped removable sine kernel integrates exactly to `arctan (x / ε)`.
The proof handles positive, negative, and zero frequencies. -/
theorem integral_exp_neg_mul_truncatedPerronIntegrand_eq_arctan_div
    (ε x : ℝ) (hε : 0 < ε) :
    ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-ε * t) * truncatedPerronIntegrand x t =
      Real.arctan (x / ε) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hpos : 0 < -x := neg_pos.mpr hx
    have h := integral_exp_neg_mul_truncatedPerronIntegrand_of_pos hε hpos
    calc
      (∫ t : ℝ in Set.Ioi 0,
          Real.exp (-ε * t) * truncatedPerronIntegrand x t) =
          -(∫ t : ℝ in Set.Ioi 0,
            Real.exp (-ε * t) * truncatedPerronIntegrand (-x) t) := by
              rw [← MeasureTheory.integral_neg]
              apply MeasureTheory.integral_congr_ae
              filter_upwards with t
              rw [truncatedPerronIntegrand_neg_left]
              ring
      _ = -Real.arctan ((-x) / ε) := by rw [h]
      _ = Real.arctan (x / ε) := by
            rw [show (-x) / ε = -(x / ε) by ring, Real.arctan_neg]
            ring
  · subst x
    simp
  · exact integral_exp_neg_mul_truncatedPerronIntegrand_of_pos hε hx

/-- The exact `Ioi` integral representation of the damped kernel. -/
theorem dampedArctanPerronKernel_eq_half_add_integral
    (ε x : ℝ) (hε : 0 < ε) :
    dampedArctanPerronKernel ε x =
      1 / 2 + (1 / Real.pi) *
        ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-ε * t) * truncatedPerronIntegrand x t := by
  rw [integral_exp_neg_mul_truncatedPerronIntegrand_eq_arctan_div ε x hε]
  unfold dampedArctanPerronKernel
  ring

/-- On the nonnegative half-line, `arctan` lies below the identity. -/
theorem arctan_le_self_of_nonneg {z : ℝ} (hz : 0 ≤ z) :
    Real.arctan z ≤ z := by
  simpa only [Real.tan_arctan] using
    Real.le_tan (Real.arctan_nonneg.mpr hz) (Real.arctan_lt_pi_div_two z)

/-- Reflection exchanges the two sides of the damped step kernel. -/
theorem dampedArctanPerronKernel_neg (ε x : ℝ) :
    dampedArctanPerronKernel ε (-x) = 1 - dampedArctanPerronKernel ε x := by
  unfold dampedArctanPerronKernel
  rw [neg_div, Real.arctan_neg]
  ring

private theorem abs_one_sub_dampedArctanPerronKernel_le
    {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    |1 - dampedArctanPerronKernel ε x| ≤ ε / (Real.pi * |x|) := by
  let z := x / ε
  have hz : 0 < z := div_pos hx hε
  have hnonneg : 0 ≤ 1 - dampedArctanPerronKernel ε x := by
    rw [sub_nonneg]
    have hdiv : Real.arctan z / Real.pi < 1 / 2 := by
      rw [div_lt_iff₀ Real.pi_pos]
      nlinarith [Real.arctan_lt_pi_div_two z]
    unfold dampedArctanPerronKernel
    rw [show x / ε = z by rfl]
    linarith
  rw [abs_of_nonneg hnonneg]
  calc
    1 - dampedArctanPerronKernel ε x = Real.arctan z⁻¹ / Real.pi := by
      rw [Real.arctan_inv_of_pos hz]
      unfold dampedArctanPerronKernel
      rw [show x / ε = z by rfl]
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ z⁻¹ / Real.pi := by
      exact (div_le_div_iff_of_pos_right Real.pi_pos).2
        (arctan_le_self_of_nonneg (inv_nonneg.mpr hz.le))
    _ = ε / (Real.pi * |x|) := by
      rw [abs_of_pos hx]
      dsimp only [z]
      field_simp [hε.ne', hx.ne', Real.pi_ne_zero]

/-- Away from the jump, exponential damping approximates the strict indicator
with the sharp elementary error `ε / (π |x|)`. -/
theorem abs_indicator_sub_dampedArctanPerronKernel_le
    {ε x : ℝ} (hε : 0 < ε) (hx : x ≠ 0) :
    |(if 0 < x then 1 else 0 : ℝ) - dampedArctanPerronKernel ε x| ≤
      ε / (Real.pi * |x|) := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hpos : 0 < -x := neg_pos.mpr hxneg
    have hbound := abs_one_sub_dampedArctanPerronKernel_le hε hpos
    rw [dampedArctanPerronKernel_neg] at hbound
    simpa [if_neg (not_lt.mpr hxneg.le), abs_neg] using hbound
  · simpa [if_pos hxpos] using
      (abs_one_sub_dampedArctanPerronKernel_le hε hxpos)

/-- At an integer half-step, the logarithmic separation converts the pointwise
damped-kernel error into the uniform bound `8 ε M / π`. -/
theorem abs_halfStepIndicator_sub_dampedArctanPerronKernel_le
    {ε : ℝ} {n Y M : ℕ} (hε : 0 < ε) (hn : n ≠ 0)
    (hM : 1 ≤ M) (hYM : Y ≤ M) :
    |(if n ≤ Y then 1 else 0 : ℝ) -
        dampedArctanPerronKernel ε
          (Real.log
            (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y / (n : ℝ)))| ≤
      8 * ε * (M : ℝ) / Real.pi := by
  let r := MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y / (n : ℝ)
  let x := Real.log r
  have hr : 0 < r :=
    MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep_div_natCast_pos hn
  have hcut : 0 < x ↔ n ≤ Y := by
    dsimp only [x]
    rw [Real.log_pos_iff hr.le]
    dsimp only [r]
    rw [one_lt_div₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    exact MathlibNt.SieveTheory.LiuWeight.natCast_lt_liuPanPerronHalfStep_iff
  have hsep : 1 / (8 * (M : ℝ)) ≤ |x| := by
    exact MathlibNt.SieveTheory.LiuWeight.one_div_eight_mul_le_abs_log_liuPanPerronHalfStep_div
      hn hM hYM
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by omega)
  have hxabs : 0 < |x| :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (8 * (M : ℝ))) hsep
  have hx : x ≠ 0 := fun hx0 => by simp [hx0] at hxabs
  have hbound := abs_indicator_sub_dampedArctanPerronKernel_le hε hx
  simp only [hcut] at hbound
  have hinv : 1 / |x| ≤ 8 * (M : ℝ) := by
    rw [div_le_iff₀ hxabs]
    rw [div_le_iff₀ (mul_pos (by norm_num) hMpos)] at hsep
    nlinarith
  calc
    |(if n ≤ Y then 1 else 0 : ℝ) -
        dampedArctanPerronKernel ε
          (Real.log
            (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y / (n : ℝ)))| =
        |(if n ≤ Y then 1 else 0 : ℝ) - dampedArctanPerronKernel ε x| := by rfl
    _ ≤ ε / (Real.pi * |x|) := hbound
    _ = (ε / Real.pi) * (1 / |x|) := by field_simp [Real.pi_ne_zero, hxabs.ne']
    _ ≤ (ε / Real.pi) * (8 * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hinv (div_nonneg hε.le Real.pi_pos.le)
    _ = 8 * ε * (M : ℝ) / Real.pi := by ring

end AnalyticNumberTheory.LargeSieve
