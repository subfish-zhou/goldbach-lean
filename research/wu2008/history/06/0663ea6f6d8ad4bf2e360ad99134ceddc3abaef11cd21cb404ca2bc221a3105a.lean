import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedBounds
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedExchange

/-!
# Wu (2004), Lemma 6.1 (6.3), before scalar feedback substitution

Source: author TeX lines 2594--2608. This is the intermediate bound with
the actual `h_delta(4)`, before (6.1) replaces it by its sigma-zero integral.
The proof performs `u = c*v`, uses the actual cross inequality, and exchanges
the triangular integral. Neither gain is assumed continuous. Weak endpoint
ordering includes the `a = b` case needed when `s = t = 3`.
-/

namespace Wu2008DoubleSieve

open Set MeasureTheory Real
open scoped Interval

theorem firstFeedbackWeighted_log_nonneg {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    0 ≤ log ((b - a * b) / (a - a * b)) := by
  rw [← firstFeedbackWeightedKernel_integral_scaled ha hab hb (by norm_num : (0 : ℝ) < 1)]
  simp only [mul_one]
  apply intervalIntegral.integral_nonneg hab
  intro u hu
  exact firstFeedbackWeightedKernel_nonneg (ha.trans_le hu.1) (hu.2.trans_lt hb)

theorem wuImprovementLimit_firstFeedback_weighted_log_intervalIntegrable
    {δ a b c : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    IntervalIntegrable (fun x => wuImprovementLimit true δ x / x *
      log ((1 - a) * (x + 1) / (a * (c - 1 - x))))
      volume (a * c - 1) (b * c - 1) := by
  have hp := firstFeedbackWeighted_parameters ha hab hb hac
  have hf := wuImprovementLimit_div_intervalIntegrable true hδ
    (by linarith : δ < 1 / 2) (a := 1) (b := 3)
    (by norm_num) (by norm_num) (by norm_num)
  exact (firstFeedbackWeighted_exchange 0 ha hab hb hp.1 hac hbc hf).2.1

/-- The actual fixed-delta intermediate inequality in (6.3), including `a = b`. -/
theorem wuImprovementLimit_firstFeedback_weighted
    {δ a b c : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hac : 2 ≤ a * c) (hbc : b * c ≤ 4) :
    log ((b - a * b) / (a - a * b)) *
      (wuImprovementLimit false δ 4 +
        ∫ x in (b * c - 1)..3, wuImprovementLimit true δ x / x) +
      (∫ x in (a * c - 1)..(b * c - 1), wuImprovementLimit true δ x / x *
        log ((1 - a) * (x + 1) / (a * (c - 1 - x)))) ≤
      ∫ v in a..b, wuImprovementLimit false δ (c * v) / (v * (1 - v)) := by
  have hp := firstFeedbackWeighted_parameters ha hab hb hac
  have hf := wuImprovementLimit_div_intervalIntegrable true hδ
    (by linarith : δ < 1 / 2) (a := 1) (b := 3)
    (by norm_num) (by norm_num) (by norm_num)
  rw [← (firstFeedbackWeighted_exchange (wuImprovementLimit false δ 4)
    ha hab hb hp.1 hac hbc hf).2.2]
  exact wuImprovementLimit_firstFeedback_weighted_nested hδ hδhi ha hab hb hac hbc

/-- Explicit degeneration of the source expression when both endpoints agree. -/
theorem firstFeedbackWeighted_diagonal (f : ℝ → ℝ) (C c : ℝ) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) :
    log ((a - a * a) / (a - a * a)) *
      (C + ∫ x in (a * c - 1)..3, f x) +
      (∫ x in (a * c - 1)..(a * c - 1),
        f x * log ((1 - a) * (x + 1) / (a * (c - 1 - x)))) = 0 := by
  have hden : a - a * a ≠ 0 := by
    have := mul_pos ha (sub_pos.mpr ha1)
    nlinarith
  simp [div_self hden]

end Wu2008DoubleSieve
