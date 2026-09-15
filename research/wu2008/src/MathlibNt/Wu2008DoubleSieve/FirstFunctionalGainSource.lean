import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainLimits

/-!
# Source logarithmic form and the explicit fixed-delta penalty

Wu04, TeX 2004--2020 and 2260--2286, especially (5.10).
The frozen F/f formulas and existing normalized recurrence identify the
coefficient, without rebuilding either delay-function theory. The source
two-parameter Psi1 is identified, but our actual H/h inequality retains
the additional `2 * delta * I / (1 - 2 * delta)` loss.
-/

namespace Wu2008DoubleSieve

open Set Real
open scoped Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem firstFunctionalGain_coefficient_eq_log {s t : ℝ}
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    wuUpperCoefficient s - wuUpperCoefficient t =
      -(∫ v in (2 : ℝ)..(t - 1), log (v - 1) / v) := by
  have hinitial (u : ℝ) (hu : 0 < u) (hu3 : u ≤ 3) : wuUpperCoefficient u = 1 := by
    unfold wuUpperCoefficient
    rw [jr1965F_eq_of_le_three hu3]
    field_simp [hu.ne', (exp_pos eulerMascheroniConstant).ne']
  have hrec := wuUpperCoefficient_sub_eq_integral (s := 3) (by norm_num) ht
  norm_num at hrec
  have hi : (∫ v in (2 : ℝ)..(t - 1), wuLowerCoefficient v / v) =
      ∫ v in (2 : ℝ)..(t - 1), log (v - 1) / v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by linarith : (2 : ℝ) ≤ t - 1)] at hv
    have ha : wuLowerCoefficient v = log (v - 1) :=
      jr1965f_normalized_firstInterval hv.1 (by linarith [hv.2])
    change wuLowerCoefficient v / v = log (v - 1) / v
    rw [ha]
  rw [hi, hinitial 3 (by norm_num) le_rfl] at hrec
  rw [hinitial s (by linarith) hs3]
  linarith

/-- The paper's two-parameter expression, not a delta-independent gain. -/
noncomputable def firstFunctionalGainPsiOne (s t : ℝ) : ℝ :=
  -(∫ v in (2 : ℝ)..(t - 1), log (v - 1) / v) +
    (1 / 2) * (∫ u in (1 - 1 / s)..(1 - 1 / t),
      log (t * u - 1) / (u * (1 - u))) - omega3XIntegralEnvelope s t

theorem firstFunctionalGainPsi_eq_log (δ : ℝ) {s t : ℝ}
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    firstFunctionalGainPsi δ s t =
      -(∫ v in (2 : ℝ)..(t - 1), log (v - 1) / v) +
        (1 / 2) * (∫ u in (1 - 1 / s)..(1 - 1 / t),
          log (t * u - 1) / (u * (1 - u))) -
        omega3XIntegralEnvelope s t / (1 - 2 * δ) := by
  unfold firstFunctionalGainPsi
  rw [firstFunctionalGain_coefficient_eq_log hs hs3 ht ht5]

theorem firstFunctionalGainPsi_eq_source_sub_penalty {δ s t : ℝ}
    (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    firstFunctionalGainPsi δ s t = firstFunctionalGainPsiOne s t -
      (2 * δ / (1 - 2 * δ)) * omega3XIntegralEnvelope s t := by
  rw [firstFunctionalGainPsi_eq_log δ hs hs3 ht ht5]
  unfold firstFunctionalGainPsiOne
  field_simp [show 1 - 2 * δ ≠ 0 by linarith]
  ring

/-- The loss is nonnegative; it cannot be dropped from a lower bound. -/
theorem firstFunctionalGain_delta_penalty_nonneg {δ s t : ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    0 ≤ (2 * δ / (1 - 2 * δ)) * omega3XIntegralEnvelope s t :=
  mul_nonneg (div_nonneg (by positivity) (by linarith))
    (omega3XIntegralEnvelope_bounds hs hst ht).1

theorem firstFunctionalGainPsi_self (δ s : ℝ) :
    firstFunctionalGainPsi δ s s = 0 := by
  simp [firstFunctionalGainPsi, omega3XIntegralEnvelope_self]

/-- Source-compatible first functional inequality for the actual gains.
Delta is fixed; the source Psi1 alone is not asserted as the gain. -/
theorem wuImprovementLimit_firstFunctionalGain_source {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    firstFunctionalGainPsiOne s t -
        (2 * δ / (1 - 2 * δ)) * omega3XIntegralEnvelope s t +
      wuImprovementLimit true δ t +
      (1 / 2) * (∫ u in (1 - 1 / s)..(1 - 1 / t),
        wuImprovementLimit false δ (t * u) / (u * (1 - u))) ≤
      wuImprovementLimit true δ s := by
  rw [← firstFunctionalGainPsi_eq_source_sub_penalty (by linarith) hs hs3 ht ht5]
  exact wuImprovementLimit_firstFunctionalGain hδ hδhi hs hs3 ht ht5 hratio

end Wu2008DoubleSieve
