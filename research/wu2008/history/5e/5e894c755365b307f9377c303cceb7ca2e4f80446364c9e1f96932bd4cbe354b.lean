import MathlibNt.Wu2008DoubleSieve.FirstFeedbackIterated
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangleContinuity
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernel
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackIndicator

/-!
# Actual scalar feedback: Wu04 Lemma 6.1 (6.1) and (6.2)

Author TeX lines 2572--2592. Apply the actual cross inequalities twice,
exchange the two triangular integrals, and solve the scalar comparison
using the proved positive denominator. Delta remains fixed throughout.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

theorem wuImprovementLimit_firstFeedback_source64 {δ v : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    wuImprovementLimit false δ 4 * log (4 / (v - 1)) +
      (∫ x in (v - 2)..3,
        wuImprovementLimit true δ x / x * log ((x + 1) / (v - 1))) ≤
      wuImprovementLimit true δ v := by
  have hf := wuImprovementLimit_div_intervalIntegrable true hδ
    (by linarith : δ < 1 / 2) (a := 1) (b := 3)
    (by norm_num) (by norm_num) (by norm_num)
  rw [← (firstFeedback_source64 hf hv hv5).2.2,
    ← firstFeedback_nested_split hδ hδhi hv hv5]
  exact wuImprovementLimit_firstFeedback_nested hδ hδhi hv hv5

theorem wuImprovementLimit_firstFeedback_scalar_raw {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    wuImprovementLimit false δ 4 * firstFeedbackSigma 3 5 4 +
      (∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x / x *
        firstFeedbackSigma 3 (x + 2) (x + 1)) ≤
      wuImprovementLimit false δ 4 := by
  have hf := wuImprovementLimit_div_intervalIntegrable true hδ
    (by linarith : δ < 1 / 2) (a := 1) (b := 3)
    (by norm_num) (by norm_num) (by norm_num)
  have hi := (firstFeedbackSigma_intervalIntegrable
    (by norm_num : (1 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 5)
    (by norm_num : (0 : ℝ) < 4)).const_mul (wuImprovementLimit false δ 4)
  have hj := (firstFeedback_scalar_exchange hf).1
  have heq : (∫ v in (3 : ℝ)..5, (∫ u in (v - 1)..4,
      (wuImprovementLimit false δ 4 +
        ∫ x in (u - 1)..3, wuImprovementLimit true δ x / x) / u) / v) =
      wuImprovementLimit false δ 4 * firstFeedbackSigma 3 5 4 +
        (∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x / x *
          firstFeedbackSigma 3 (x + 2) (x + 1)) := by
    calc
      _ = ∫ v in (3 : ℝ)..5,
          wuImprovementLimit false δ 4 * (log (4 / (v - 1)) / v) +
          (∫ x in (v - 2)..3, wuImprovementLimit true δ x / x *
            log ((x + 1) / (v - 1))) / v := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)]
        intro v hv
        dsimp only
        rw [firstFeedback_nested_split hδ hδhi hv.1 hv.2,
          (firstFeedback_source64 hf hv.1 hv.2).2.2]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add hi hj,
          intervalIntegral.integral_const_mul, (firstFeedback_scalar_exchange hf).2.2]
        rfl
  rw [← heq]
  exact wuImprovementLimit_firstFeedback_iterated hδ hδhi

/-- Wu04 (6.1), for the actual fixed-delta limiting gains. -/
theorem wuImprovementLimit_firstFeedback_61 {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    (∫ x in (1 : ℝ)..3,
      wuImprovementLimit true δ x * firstFeedbackSigmaZero x / x) ≤
      wuImprovementLimit false δ 4 := by
  have h := wuImprovementLimit_firstFeedback_scalar_raw hδ hδhi
  have hd := firstFeedbackSigma_denominator_pos
  have heq : (∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x / x *
      firstFeedbackSigma 3 (x + 2) (x + 1)) =
      (1 - firstFeedbackSigma 3 5 4) *
        ∫ x in (1 : ℝ)..3,
          wuImprovementLimit true δ x * firstFeedbackSigmaZero x / x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [firstFeedbackSigmaZero]
    field_simp
  rw [heq] at h
  nlinarith

theorem wuImprovementLimit_firstFeedback_62_split {δ v : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    (∫ x in (1 : ℝ)..3,
      wuImprovementLimit true δ x * firstFeedbackSigmaZero x / x) *
        log (4 / (v - 1)) +
      (∫ x in (v - 2)..3,
        wuImprovementLimit true δ x / x * log ((x + 1) / (v - 1))) ≤
      wuImprovementLimit true δ v := by
  have hl : 0 ≤ log (4 / (v - 1)) :=
    Real.log_nonneg ((le_div_iff₀ (by linarith : 0 < v - 1)).2 (by linarith))
  have hmul := mul_le_mul_of_nonneg_right
    (wuImprovementLimit_firstFeedback_61 hδ hδhi) hl
  have hsource := wuImprovementLimit_firstFeedback_source64 hδ hδhi hv hv5
  linarith

/-- The literal closed-indicator form of Wu04 (6.2). -/
theorem wuImprovementLimit_firstFeedback_62 {δ v : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    (∫ x in (1 : ℝ)..3, wuImprovementLimit true δ x *
      (firstFeedbackSigmaZero x / x * log (4 / (v - 1)) +
        (Icc (v - 2) 3).indicator (fun _ : ℝ => (1 : ℝ)) x / x *
          log ((x + 1) / (v - 1)))) ≤ wuImprovementLimit true δ v := by
  have hf := wuImprovementLimit_div_intervalIntegrable true hδ
    (by linarith : δ < 1 / 2) (a := 1) (b := 3)
    (by norm_num) (by norm_num) (by norm_num)
  have hi := (firstFeedbackSigmaZero_gain_intervalIntegrable true hδ
    (by linarith : δ < 1 / 2)).mul_const (log (4 / (v - 1)))
  have hj := firstFeedback_indicator_intervalIntegrable (by linarith : v - 2 ≤ 3)
    (firstFeedback_source64 hf hv hv5).2.1
  have heq (x : ℝ) :
      wuImprovementLimit true δ x *
        (firstFeedbackSigmaZero x / x * log (4 / (v - 1)) +
          (Icc (v - 2) 3).indicator (fun _ : ℝ => (1 : ℝ)) x / x *
            log ((x + 1) / (v - 1))) =
      wuImprovementLimit true δ x * firstFeedbackSigmaZero x / x *
        log (4 / (v - 1)) +
      (Icc (v - 2) 3).indicator (fun x => wuImprovementLimit true δ x / x *
        log ((x + 1) / (v - 1))) x := by
    by_cases hx : x ∈ Icc (v - 2) 3
    · simp only [indicator_of_mem hx]
      ring
    · simp only [indicator_of_notMem hx]
      ring
  simp_rw [heq]
  rw [intervalIntegral.integral_add hi hj, intervalIntegral.integral_mul_const,
    firstFeedback_indicator_integral _ (by linarith : 1 ≤ v - 2)
      (by linarith : v - 2 ≤ 3) (by norm_num)]
  exact wuImprovementLimit_firstFeedback_62_split hδ hδhi hv hv5

end Wu2008DoubleSieve
