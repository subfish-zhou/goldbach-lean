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

theorem firstFeedbackWeightedKernel_continuousOn {A B c : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hBc : B < c) :
    ContinuousOn (firstFeedbackWeightedKernel c) (uIcc A B) := by
  apply continuousOn_const.div
    (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
  rw [uIcc_of_le hAB]
  intro u hu
  exact mul_ne_zero (ne_of_gt (hA.trans_le hu.1))
    (ne_of_gt (sub_pos.mpr (hu.2.trans_lt hBc)))

theorem firstFeedbackWeightedKernel_nonneg {c u : ℝ}
    (hu : 0 < u) (huc : u < c) : 0 ≤ firstFeedbackWeightedKernel c u := by
  exact (div_pos (hu.trans huc) (mul_pos hu (sub_pos.mpr huc))).le

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

/-- Literal linear substitution `u = c*v`, valid even without integrability. -/
theorem firstFeedbackWeighted_substitution (g : ℝ → ℝ) {a b c : ℝ}
    (hc : c ≠ 0) :
    (∫ v in a..b, g (c * v) / (v * (1 - v))) =
      ∫ u in (a * c)..(b * c), g u * firstFeedbackWeightedKernel c u := by
  have heq (v : ℝ) :
      g (c * v) / (v * (1 - v)) =
        c * (g (c * v) * firstFeedbackWeightedKernel c (c * v)) := by
    dsimp [firstFeedbackWeightedKernel]
    rw [show c - c * v = c * (1 - v) by ring]
    field_simp
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul]
  simpa only [smul_eq_mul, mul_comm c a, mul_comm c b] using
    intervalIntegral.smul_integral_comp_mul_left
      (a := a) (b := b) (fun u => g u * firstFeedbackWeightedKernel c u) c

theorem firstFeedbackWeightedKernel_integral_scaled {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hc : 0 < c) :
    (∫ u in (a * c)..(b * c), firstFeedbackWeightedKernel c u) =
      log ((b - a * b) / (a - a * b)) := by
  rw [firstFeedbackWeightedKernel_integral (mul_pos ha hc)
    (mul_le_mul_of_nonneg_right hab hc.le) (by nlinarith)]
  congr 1
  field_simp

theorem firstFeedbackWeightedKernel_integral_partial {a c x : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hx : a * c - 1 ≤ x) (hxc : x + 1 < c) :
    (∫ u in (a * c)..(x + 1), firstFeedbackWeightedKernel c u) =
      log ((1 - a) * (x + 1) / (a * (c - 1 - x))) := by
  rw [firstFeedbackWeightedKernel_integral (mul_pos ha hc) (by linarith) hxc]
  congr 1
  field_simp
  ring

/-- The composed source integral is integrable whenever the original gain is;
continuity is required only for its nonsingular scalar weight. -/
theorem firstFeedbackWeighted_intervalIntegrable {g : ℝ → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hc : c ≠ 0)
    (hg : IntervalIntegrable g volume (a * c) (b * c)) :
    IntervalIntegrable (fun v => g (c * v) / (v * (1 - v))) volume a b := by
  have hcomp : IntervalIntegrable (fun v => g (c * v)) volume a b := by
    simpa only [mul_div_cancel_right₀ a hc, mul_div_cancel_right₀ b hc] using
      (hg.comp_mul_left (c := c))
  have hweight : ContinuousOn (fun v : ℝ => (v * (1 - v))⁻¹) (uIcc a b) := by
    apply (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).inv₀
    rw [uIcc_of_le hab]
    intro v hv
    exact mul_ne_zero (ne_of_gt (ha.trans_le hv.1))
      (ne_of_gt (sub_pos.mpr (hv.2.trans_lt hb)))
  simpa only [div_eq_mul_inv] using hcomp.mul_continuousOn hweight

end Wu2008DoubleSieve
