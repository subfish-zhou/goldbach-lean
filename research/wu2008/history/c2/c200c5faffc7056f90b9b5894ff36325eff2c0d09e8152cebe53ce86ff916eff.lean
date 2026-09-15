import MathlibNt.Wu2008DoubleSieve.ReboxingParameterSource

/-!
# Quantitative width of the actual replacement parameters

Wu04 source lines 1046--1065 and 1128--1149. This supplies the geometric
input to the R2 estimate, not the remaining prime-counting/payment argument.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem reboxing_parameter_width {q Δ t j : ℝ} {i : ℕ}
    (hq : 1 < q) (hΔ : 1 < Δ) (ht : 0 < t) (ht10 : t ≤ 10) (hj : 1 ≤ j) :
    0 ≤ reboxingS2 q Δ t i j - reboxingS1 q Δ t j ∧
      reboxingS2 q Δ t i j - reboxingS1 q Δ t j ≤
        (100 + 10 * (i : ℝ)) * log Δ / log q := by
  have hq0 : 0 < q := by linarith
  have hΔ0 : 0 < Δ := by linarith
  have hL : 0 < log q := log_pos hq
  have hE : 0 < log Δ := log_pos hΔ
  have hm := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
  have ha0 : 1 < reboxingAlpha q Δ t 0 := by
    rw [reboxingAlpha_zero]
    exact one_lt_rpow hq (by positivity)
  have hB1 : 1 < reboxingAlpha q Δ t (j - 1) := ha0.trans_le (hm (by linarith))
  have hC1 : 1 < reboxingAlpha q Δ t j := ha0.trans_le (hm (by linarith))
  have hB : 0 < log (reboxingAlpha q Δ t (j - 1)) := log_pos hB1
  have hC : 0 < log (reboxingAlpha q Δ t j) := log_pos hC1
  have hBC : log (reboxingAlpha q Δ t j) =
      log (reboxingAlpha q Δ t (j - 1)) + log Δ := by
    rw [reboxingAlpha_log hq0 hΔ0, reboxingAlpha_log hq0 hΔ0]
    ring
  have hBlow : log q / 10 ≤ log (reboxingAlpha q Δ t (j - 1)) := by
    rw [reboxingAlpha_log hq0 hΔ0]
    have hh := div_le_div_of_nonneg_left hL.le ht ht10
    nlinarith
  have hClow : log q / 10 ≤ log (reboxingAlpha q Δ t j) := by linarith
  have hquot : log q / log (reboxingAlpha q Δ t j) ≤ 10 :=
    (div_le_iff₀ hC).2 (by linarith)
  have hEquot : log Δ / log (reboxingAlpha q Δ t (j - 1)) ≤ 10 * log Δ / log q := by
    calc
      _ ≤ log Δ / (log q / 10) :=
        div_le_div_of_nonneg_left hE.le (by positivity) hBlow
      _ = _ := by ring
  have he : reboxingS2 q Δ t i j - reboxingS1 q Δ t j =
      (log q / log (reboxingAlpha q Δ t j) + (i : ℝ)) *
        (log Δ / log (reboxingAlpha q Δ t (j - 1))) := by
    rw [reboxingS1_formula hq0 hΔ0 hC1, reboxingS2_formula hq0 hΔ0 hB1]
    field_simp
    rw [hBC]
    ring
  rw [he]
  constructor
  · positivity
  · calc
      _ ≤ (10 + (i : ℝ)) * (10 * log Δ / log q) := by
        apply mul_le_mul (by linarith : log q / log (reboxingAlpha q Δ t j) +
          (i : ℝ) ≤ 10 + (i : ℝ)) hEquot
        · positivity
        · positivity
      _ = _ := by ring

/-- Uniform, explicit `log(N)^(-5)` replacement width on every legal
source box. This uses the literal mesh upper bound, not an eventual
pointwise convergence assumption for an improvement coefficient. -/
theorem reboxing_source_parameter_width {i k N : ℕ} {δ Δ t j : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hL : 1 ≤ log (N : ℝ)) (hb : wuSourceBox k δ N i Δ V)
    (ht : 0 < t) (ht10 : t ≤ 10) (hj : 1 ≤ j) :
    let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
    0 ≤ reboxingS2 q Δ t i j - reboxingS1 q Δ t j ∧
      reboxingS2 q Δ t i j - reboxingS1 q Δ t j ≤
        ((200 + 20 * (k : ℝ)) / δ ^ (k + 1)) / log (N : ℝ) ^ (5 : ℕ) := by
  dsimp only
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  have hL0 : 0 < log (N : ℝ) := by linarith
  have hΔ : 1 < Δ := by
    have hh := rpow_pos_of_pos hL0 (-4 : ℝ)
    linarith [hb.2.1]
  have hΔlog : log Δ ≤ 2 / log (N : ℝ) ^ (4 : ℕ) := by
    have hh := log_le_sub_one_of_pos (by linarith : 0 < Δ)
    have hp : log (N : ℝ) ^ (-4 : ℝ) = 1 / log (N : ℝ) ^ (4 : ℕ) := by
      rw [rpow_neg hL0.le]
      norm_num
    have hhi := hb.2.2.1
    rw [hp, mul_one_div] at hhi
    linarith
  have ha : 0 < δ ^ (k + 1) := pow_pos hδ _
  have hqlo := reboxing_box_level_ge_lower hN hδ hδhi hb
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hq : 1 < q := (one_lt_rpow hN1 ha).trans_le hqlo
  have hlogq : δ ^ (k + 1) * log (N : ℝ) ≤ log q := by
    have hh := log_le_log (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _) hqlo
    simpa only [log_rpow (by linarith : (0 : ℝ) < N)] using hh
  have hw := reboxing_parameter_width (i := i) hq hΔ ht ht10 hj
  refine ⟨hw.1, hw.2.trans ?_⟩
  have hik : (i : ℝ) ≤ k := by exact_mod_cast hb.1
  calc
    _ ≤ ((100 + 10 * (k : ℝ)) * (2 / log (N : ℝ) ^ (4 : ℕ))) /
        (δ ^ (k + 1) * log (N : ℝ)) := by
      apply div_le_div₀
      · positivity
      · apply mul_le_mul (by linarith : 100 + 10 * (i : ℝ) ≤ 100 + 10 * (k : ℝ))
          hΔlog (log_pos hΔ).le (by positivity)
      · positivity
      · exact hlogq
    _ = _ := by
      rw [show (5 : ℕ) = 4 + 1 by norm_num, pow_succ]
      field_simp
      ring

/-- The R2 replacement cutoff has logarithmic-logarithmic width no
larger than `s2-s1`. The source hypotheses of this scalar fact are
produced atom by atom by `reboxing_source_parameters`. -/
theorem reboxing_replacement_log_width {D p a b : ℝ}
    (hD : 0 < D) (hp : 1 < p) (ha : 1 ≤ a)
    (hau : a ≤ log D / log p - 1) (hub : log D / log p - 1 ≤ b) :
    1 ≤ log ((D / p) ^ (1 / a)) / log p ∧
      log (log ((D / p) ^ (1 / a)) / log p) ≤ b - a := by
  have hp0 : 0 < p := by linarith
  have hLp : 0 < log p := log_pos hp
  have ha0 : 0 < a := by linarith
  have he : log ((D / p) ^ (1 / a)) / log p =
      (log D / log p - 1) / a := by
    rw [log_rpow (div_pos hD hp0), log_div hD.ne' hp0.ne']
    field_simp
  rw [he]
  have hratio : 1 ≤ (log D / log p - 1) / a := (one_le_div ha0).2 hau
  refine ⟨hratio, ?_⟩
  have hlog := log_le_sub_one_of_pos (by linarith :
    0 < (log D / log p - 1) / a)
  have hdiff : (log D / log p - 1) / a - 1 =
      ((log D / log p - 1) - a) / a := by field_simp
  have hdiv : ((log D / log p - 1) - a) / a ≤ (log D / log p - 1) - a :=
    div_le_self (sub_nonneg.mpr hau) ha
  rw [hdiff] at hlog
  linarith

end Wu2008DoubleSieve
