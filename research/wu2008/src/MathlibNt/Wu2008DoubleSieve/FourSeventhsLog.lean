import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabLaplace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Wu2008DoubleSieve.SecondFunctionalFourSevenths
open Set Real MeasureTheory LiLiuPrereqBuchstab SecondFunctionalJointTail

/-- The reciprocal lies below its chord on a positive interval. -/
theorem reciprocal_chord {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hx : x ∈ Icc a b) : 1 / x ≤ (a + b - x) / (a * b) := by
  have hb : 0 < b := ha.trans_le hab
  have hxp : 0 < x := ha.trans_le hx.1
  apply (div_le_iff₀ hxp).2
  rw [div_mul_eq_mul_div]
  have hprod : 0 ≤ (x - a) * (b - x) := mul_nonneg (sub_nonneg.mpr hx.1)
    (sub_nonneg.mpr hx.2)
  apply (le_div_iff₀ (mul_pos ha hb)).2
  nlinarith

/-- Exact integral comparison; no quadrature or finite sampling is involved. -/
theorem log_chord_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    log (b / a) ≤ (b - a) * (1 / a + 1 / b) / 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hi : IntervalIntegrable (fun x : ℝ => 1 / x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ne_of_gt (ha.trans_le hx.1)
  have hc : IntervalIntegrable (fun x : ℝ => (a + b - x) / (a * b)) volume a b :=
    (by fun_prop : Continuous (fun x : ℝ => (a + b - x) / (a * b))).intervalIntegrable a b
  have h := intervalIntegral.integral_mono_on hab hi hc
    (fun x hx => reciprocal_chord ha hab hx)
  rw [integral_one_div_of_pos ha hb] at h
  have he : (∫ x : ℝ in a..b, (a + b - x) / (a * b)) =
      (b - a) * (1 / a + 1 / b) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (f := fun _ : ℝ => a + b) (g := fun x : ℝ => x)
      intervalIntegrable_const (continuous_id.intervalIntegrable a b),
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    field_simp
    ring
  exact he ▸ h

/-- Two fixed reciprocal chords provide the required rational logarithm seed. -/
theorem log_seven_fourths_le : log (7 / 4 : ℝ) ≤ 699 / 1232 := by
  have h1 := log_chord_bound (a := (1 : ℝ)) (b := 11 / 8) (by norm_num) (by norm_num)
  have h2 := log_chord_bound (a := (11 / 8 : ℝ)) (b := 7 / 4) (by norm_num) (by norm_num)
  rw [log_div (by norm_num) (by norm_num)] at h2
  norm_num at h1 h2
  linarith

/-- A tangent at the fixed seed controls every positive argument. -/
theorem log_tangent_four_sevenths {y : ℝ} (hy : 0 < y) :
    log y ≤ (4 / 7 : ℝ) * y - 3 / 7 := by
  have h := log_le_sub_one_of_pos (div_pos hy (by norm_num : (0 : ℝ) < 7 / 4))
  rw [log_div (ne_of_gt hy) (by norm_num)] at h
  have hs := log_seven_fourths_le
  linarith

end Wu2008DoubleSieve.SecondFunctionalFourSevenths
