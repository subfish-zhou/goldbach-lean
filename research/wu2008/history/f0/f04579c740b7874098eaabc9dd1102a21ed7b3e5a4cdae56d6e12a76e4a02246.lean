import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeighted
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackScalar
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackParameters

/-!
# Actual weighted feedback: Wu04 Lemma 6.1 (6.3)

Author TeX lines 2594--2610. The proved positive logarithmic multiplier
allows the actual scalar bound (6.1) to replace `h_delta(4)`.
Closed source indicators are transported separately. Weak endpoint
ordering includes the zero-length case.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

theorem wuImprovementLimit_firstFeedback_63_split {δ a b c : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    log ((b - a * b) / (a - a * b)) *
      ((∫ x in (1 : ℝ)..3,
        wuImprovementLimit true δ x * firstFeedbackSigmaZero x / x) +
        ∫ x in (b * c - 1)..3, wuImprovementLimit true δ x / x) +
      (∫ x in (a * c - 1)..(b * c - 1), wuImprovementLimit true δ x / x *
        log ((1 - a) * (x + 1) / (a * (c - 1 - x)))) ≤
      ∫ v in a..b, wuImprovementLimit false δ (c * v) / (v * (1 - v)) := by
  have hmul := mul_le_mul_of_nonneg_left
    (wuImprovementLimit_firstFeedback_61 hδ hδhi)
    (firstFeedbackWeighted_log_nonneg ha hab hb)
  have hw := wuImprovementLimit_firstFeedback_weighted hδ hδhi ha hab hb hac hbc
  nlinarith

/-- The literal closed-indicator source expression (6.3), with `a = b` allowed. -/
theorem wuImprovementLimit_firstFeedback_63 {δ a b c : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    log ((b - a * b) / (a - a * b)) *
      (∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x *
        (firstFeedbackSigmaZero x +
          (Icc (b * c - 1) 3).indicator (fun _ : ℝ => (1 : ℝ)) x) / x) +
      (∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x *
        (Icc (a * c - 1) (b * c - 1)).indicator (fun _ : ℝ => (1 : ℝ)) x / x *
          log ((1 - a) * (x + 1) / (a * (c - 1 - x)))) ≤
      ∫ v in a..b, wuImprovementLimit false δ (c * v) / (v * (1 - v)) := by
  have hp := firstFeedbackWeighted_parameters ha hab hb hac
  have hbc1 : 1 ≤ b * c - 1 := by linarith [hp.2.1]
  have hbc3 : b * c - 1 ≤ 3 := by linarith
  have hab' : a * c - 1 ≤ b * c - 1 := by linarith [hp.2.1]
  have hi := firstFeedbackSigmaZero_gain_intervalIntegrable true hδ
    (by linarith : δ < 1 / 2)
  have hj := firstFeedback_indicator_intervalIntegrable hbc3
    (wuImprovementLimit_div_intervalIntegrable true hδ (by linarith : δ < 1 / 2)
      hbc1 hbc3 (by norm_num))
  have heq1 (x : ℝ) : wuImprovementLimit true δ x *
        (firstFeedbackSigmaZero x +
          (Icc (b * c - 1) 3).indicator (fun _ : ℝ => (1 : ℝ)) x) / x =
      wuImprovementLimit true δ x * firstFeedbackSigmaZero x / x +
        (Icc (b * c - 1) 3).indicator
          (fun x => wuImprovementLimit true δ x / x) x := by
    by_cases hx : x ∈ Icc (b * c - 1) 3
    · simp only [indicator_of_mem hx]
      ring
    · simp only [indicator_of_notMem hx]
      ring
  have heq2 (x : ℝ) : wuImprovementLimit true δ x *
        (Icc (a * c - 1) (b * c - 1)).indicator (fun _ : ℝ => (1 : ℝ)) x / x *
          log ((1 - a) * (x + 1) / (a * (c - 1 - x))) =
      (Icc (a * c - 1) (b * c - 1)).indicator (fun x =>
        wuImprovementLimit true δ x / x *
          log ((1 - a) * (x + 1) / (a * (c - 1 - x)))) x := by
    by_cases hx : x ∈ Icc (a * c - 1) (b * c - 1)
    · simp only [indicator_of_mem hx, mul_one]
    · simp only [indicator_of_notMem hx, mul_zero, zero_div, zero_mul]
  simp_rw [heq1, heq2]
  rw [intervalIntegral.integral_add hi hj,
    firstFeedback_indicator_integral _ hbc1 hbc3 (by norm_num),
    firstFeedback_indicator_integral _ (by linarith : 1 ≤ a * c - 1) hab' hbc3]
  exact wuImprovementLimit_firstFeedback_63_split hδ hδhi ha hab hb hac hbc

/-- The precise parameter substitution used in the proof of Proposition 3. -/
theorem wuImprovementLimit_firstFeedback_63_parameters {δ s t : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    log ((t - 1) / (s - 1)) *
      ((∫ x in (1 : ℝ)..3,
        wuImprovementLimit true δ x * firstFeedbackSigmaZero x / x) +
        ∫ x in (t - 2)..3, wuImprovementLimit true δ x / x) +
      (∫ x in (t - t / s - 1)..(t - 2), wuImprovementLimit true δ x / x *
        log ((x + 1) / ((s - 1) * (t - 1 - x)))) ≤
      ∫ v in (1 - 1 / s)..(1 - 1 / t),
        wuImprovementLimit false δ (t * v) / (v * (1 - v)) := by
  obtain ⟨ha, hab, hb, hac, hbc⟩ :=
    firstFeedback_parameter_domain hs hs3 ht ht5 hratio
  have h := wuImprovementLimit_firstFeedback_63_split hδ hδhi ha hab hb hac hbc
  have heqa : (1 - 1 / s) * t - 1 = t - t / s - 1 := by ring
  have heqb : (1 - 1 / t) * t - 1 = t - 2 := by
    have ht0 : t ≠ 0 := by linarith
    field_simp
    ring
  rw [firstFeedback_parameter_log_ratio (by linarith : 1 < s)
    (by linarith : 1 < t), heqa, heqb] at h
  simpa only [firstFeedback_parameter_inner_ratio (by linarith : 1 < s)] using h

end Wu2008DoubleSieve
