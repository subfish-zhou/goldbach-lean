import MathlibNt.Wu2008DoubleSieve.ReboxingParameterSource

/-!
# Actual terminal boundary geometry for R1

Wu04 source lines 1115--1127, following (3.16). The lower endpoint
is the actual terminal geometric endpoint, not a selected prime.
The result includes a zero terminal index and depth zero.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

/-- The literal R1 endpoints have polynomial height and a uniformly
short logarithmic ratio. The terminal inequalities are furnished by
`reboxingAlpha_exists_terminal` or `reboxing_source_parameters`. -/
theorem reboxing_terminal_boundary_geometry {i k N r : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hL : 1 ≤ log (N : ℝ)) (hb : wuSourceBox k δ N i Δ V)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hrlo : reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s))
    (hrhi : ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) <
      reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (r + 1)) :
    let Y := reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r
    (N : ℝ) ^ (δ ^ (k + 1) / 10) ≤ Y ∧
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        Y ≤ wuLocalCutoff N δ d s ∧
          log (wuLocalCutoff N δ d s / Y) ≤
            (2 + (k : ℝ)) / log (N : ℝ) ^ (4 : ℕ) := by
  dsimp only
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  let Y := reboxingAlpha q Δ t r
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 < log (N : ℝ) := by linarith
  have hΔ : 1 < Δ := by
    have hh := rpow_pos_of_pos hL0 (-4 : ℝ)
    linarith [hb.2.1]
  have hΔ0 : 0 < Δ := by linarith
  have hΔlog : log Δ ≤ 2 / log (N : ℝ) ^ (4 : ℕ) := by
    have hh := log_le_sub_one_of_pos hΔ0
    have hp : log (N : ℝ) ^ (-4 : ℝ) = 1 / log (N : ℝ) ^ (4 : ℕ) := by
      rw [rpow_neg hL0.le]
      norm_num
    have hhi := hb.2.2.1
    rw [hp, mul_one_div] at hhi
    linarith
  have ha : 0 < δ ^ (k + 1) := pow_pos hδ _
  have hqlo := reboxing_box_level_ge_lower hN hδ hδhi hb
  have hq : 1 < q := (one_lt_rpow hN1 ha).trans_le hqlo
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hY0 : 0 < Y := reboxingAlpha_pos hq0 hΔ0
  have hYlo : q ^ (1 / t) ≤ Y := by
    have hh := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
      (show (0 : ℝ) ≤ r by positivity)
    simpa only [reboxingAlpha_zero] using hh
  constructor
  · calc
      _ = ((N : ℝ) ^ (δ ^ (k + 1))) ^ (1 / 10 : ℝ) := by
        rw [← rpow_mul hN0.le]
        congr 1
        ring
      _ ≤ q ^ (1 / 10 : ℝ) := rpow_le_rpow (rpow_nonneg hN0.le _) hqlo (by norm_num)
      _ ≤ q ^ (1 / t) :=
        rpow_le_rpow_of_exponent_le hq.le (one_div_le_one_div_of_le ht0 ht)
      _ ≤ Y := hYlo
  · intro d hd
    have hV : ∀ l, 0 < V l := fun l =>
      (rpow_pos_of_pos hN0 _).trans_le (hb.2.2.2.2.1 l)
    have hcuts := reboxing_support_cutoff_bounds
      (rpow_nonneg hN0.le (1 / 2 - δ)) hΔ0 hV hs0 hd
    have hlow : Y ≤ wuLocalCutoff N δ d s := hrlo.trans hcuts.1
    refine ⟨hlow, ?_⟩
    have hterm : q ^ (1 / s) ≤ Y * Δ := by
      have hh := hrhi.le
      rw [reboxingAlpha_step hΔ0] at hh
      exact hh
    have hhigh : wuLocalCutoff N δ d s ≤ Y * Δ ^ (1 + (i : ℝ) / s) := by
      calc
        _ ≤ q ^ (1 / s) * Δ ^ ((i : ℝ) / s) := hcuts.2
        _ ≤ (Y * Δ) * Δ ^ ((i : ℝ) / s) :=
          mul_le_mul_of_nonneg_right hterm (rpow_nonneg hΔ0.le _)
        _ = _ := by rw [rpow_add hΔ0, rpow_one]; ring
    have hratio : wuLocalCutoff N δ d s / Y ≤ Δ ^ (1 + (i : ℝ) / s) :=
      (div_le_iff₀ hY0).2 (by simpa only [mul_comm] using hhigh)
    have hZ0 : 0 < wuLocalCutoff N δ d s := hY0.trans_le hlow
    have hlog := log_le_log (div_pos hZ0 hY0) hratio
    rw [log_rpow hΔ0] at hlog
    have hik : (i : ℝ) ≤ k := by exact_mod_cast hb.1
    have his : (i : ℝ) / s ≤ (k : ℝ) / 2 := by
      calc
        _ ≤ (i : ℝ) / 2 := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) hs
        _ ≤ _ := div_le_div_of_nonneg_right hik (by norm_num)
    calc
      _ ≤ (1 + (i : ℝ) / s) * log Δ := hlog
      _ ≤ (1 + (k : ℝ) / 2) * (2 / log (N : ℝ) ^ (4 : ℕ)) := by
        apply mul_le_mul (by linarith) hΔlog (log_pos hΔ).le (by positivity)
      _ = _ := by ring

end Wu2008DoubleSieve
