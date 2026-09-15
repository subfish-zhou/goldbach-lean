import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSource

/-!
# Exact parameters in Wu04 Proposition 3

Author TeX lines 2614--2619 substitutes `a = 1 - 1/s`, `b = 1 - 1/t`,
and `c = t` in Lemma 6.1. These identities retain the coincident endpoint
`s = t = 3`. No strict inequality between the two integration endpoints
is introduced.
-/

namespace Wu2008DoubleSieve

open Real

theorem firstFeedback_parameter_domain {s t : ℝ}
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    0 < 1 - 1 / s ∧ 1 - 1 / s ≤ 1 - 1 / t ∧ 1 - 1 / t < 1 ∧
      2 ≤ (1 - 1 / s) * t ∧ (1 - 1 / t) * t ≤ 4 := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hst : s ≤ t := hs3.trans ht
  have hsinv : 1 / s < 1 := (div_lt_one hs0).2 (by linarith)
  have htin : 0 < 1 / t := one_div_pos.mpr ht0
  have heqa : (1 - 1 / s) * t = t - t / s := by ring
  have heqb : (1 - 1 / t) * t = t - 1 := by
    field_simp
  refine ⟨by linarith, sub_le_sub_left
    (one_div_le_one_div_of_le hs0 hst) 1, by linarith, ?_, ?_⟩
  · rwa [heqa]
  · rw [heqb]
    linarith

theorem firstFeedback_parameter_log_ratio {s t : ℝ}
    (hs : 1 < s) (ht : 1 < t) :
    log (((1 - 1 / t) - (1 - 1 / s) * (1 - 1 / t)) /
      ((1 - 1 / s) - (1 - 1 / s) * (1 - 1 / t))) =
      log ((t - 1) / (s - 1)) := by
  congr 1
  have hs0 : s ≠ 0 := by linarith
  have ht0 : t ≠ 0 := by linarith
  have ha : (1 - 1 / s) - (1 - 1 / s) * (1 - 1 / t) ≠ 0 := by
    have hpos : 0 < (1 - 1 / s) * (1 / t) :=
      mul_pos (by have := (div_lt_one (show 0 < s by linarith)).2 hs; linarith)
        (one_div_pos.mpr (by linarith))
    nlinarith
  field_simp
  ring

theorem firstFeedback_parameter_inner_ratio {s t x : ℝ}
    (hs : 1 < s) :
    (1 - (1 - 1 / s)) * (x + 1) /
      ((1 - 1 / s) * (t - 1 - x)) =
      (x + 1) / ((s - 1) * (t - 1 - x)) := by
  have hs0 : s ≠ 0 := by linarith
  rw [show 1 - (1 - 1 / s) = 1 / s by ring,
    show 1 - 1 / s = (s - 1) / s by field_simp]
  convert (div_div_div_cancel_right₀ hs0 (x + 1)
    ((s - 1) * (t - 1 - x))) using 1
  ring

theorem firstFeedback_sigma_log_coefficient {s t : ℝ}
    (hs : 1 < s) (ht : 1 < t) :
    log (4 / (t - 1)) + (1 / 2) * log ((t - 1) / (s - 1)) =
      (1 / 2) * log (16 / ((s - 1) * (t - 1))) := by
  have hs0 : s - 1 ≠ 0 := by linarith
  have ht0 : t - 1 ≠ 0 := by linarith
  have h16 : log (16 : ℝ) = 2 * log 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, log_pow]
    norm_num
  rw [log_div (by norm_num) ht0, log_div ht0 hs0,
    log_div (by norm_num) (mul_ne_zero hs0 ht0), log_mul hs0 ht0, h16]
  ring

theorem firstFeedback_tail_log_coefficient {s t x : ℝ}
    (hs : 1 < s) (ht : 1 < t) (hx : -1 < x) :
    log ((x + 1) / (t - 1)) + (1 / 2) * log ((t - 1) / (s - 1)) =
      (1 / 2) * log ((x + 1) ^ 2 / ((s - 1) * (t - 1))) := by
  have hs0 : s - 1 ≠ 0 := by linarith
  have ht0 : t - 1 ≠ 0 := by linarith
  have hx0 : x + 1 ≠ 0 := by linarith
  rw [log_div hx0 ht0, log_div ht0 hs0,
    log_div (pow_ne_zero 2 hx0) (mul_ne_zero hs0 ht0),
    log_mul hs0 ht0, log_pow]
  norm_num
  ring

end Wu2008DoubleSieve
