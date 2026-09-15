import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPaySecondaryLocal

/-! Small-power bounds for logarithms, divisor counts and completed moduli. -/
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Uniform from x=1, rather than an eventual bound with a varying cutoff. -/
theorem directPaySecondary_log {δ x H : ℝ} (hδ : 0 < δ) (hx : 1 ≤ x)
    (hH : 0 < H) (hHx : H ≤ 8 * x ^ (6 : ℕ)) :
    1 + Real.log (2 * H) ≤ (1 + Real.log 16 + 6 / δ) * x ^ δ := by
  have hx0 : 0 < x := by linarith
  have he := Real.one_le_rpow hx hδ.le
  have hl := Real.log_le_log (by positivity : 0 < 2 * H)
    (show 2 * H ≤ 16 * x ^ (6 : ℕ) by linarith)
  rw [Real.log_mul (x := 16) (by norm_num) (by positivity), Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have ht := Real.log_le_rpow_div hx0.le hδ
  have hc : 0 ≤ 1 + Real.log 16 := by positivity
  have hh := mul_le_mul_of_nonneg_left he hc
  calc
    _ ≤ 1 + Real.log 16 + 6 * Real.log x := by linarith
    _ ≤ 1 + Real.log 16 + 6 * (x ^ δ / δ) := by linarith
    _ ≤ (1 + Real.log 16 + 6 / δ) * x ^ δ := by
      calc
        _ ≤ (1 + Real.log 16) * x ^ δ + 6 * (x ^ δ / δ) := by linarith
        _ = _ := by ring

/-- A fixed tau constant precedes x and the signed shift. -/
theorem directPaySecondary_tau {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ca : ℝ, 0 < Ca ∧ ∀ (x : ℝ), 1 ≤ x → ∀ a : ℤ, |(a : ℝ)| ≤ x →
      (a.natAbs.divisors.card : ℝ) ≤ Ca * x ^ δ := by
  obtain ⟨Ca, hCa, ht⟩ := direct_tau_subpower 2 hδ
  refine ⟨Ca, hCa, ?_⟩
  intro x hx a ha
  have habs : (a.natAbs : ℝ) ≤ x := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    exact ha
  simpa only [fouvryTau_two] using ht x hx a.natAbs habs

/-- Exact root algebra, retaining the Weil excess power as its own factor. -/
theorem directPaySecondary_root_algebra {n r s V : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (_hV : 0 ≤ V) (κ : ℝ) :
    (16 * n * r * s * s) ^ (1 / 2 + κ : ℝ) *
      (2 * r * Real.sqrt (8 * n * s * s * V)) =
    (8 * Real.sqrt 8) * (16 * n * r * s * s) ^ κ * Real.sqrt V *
      n * r * Real.sqrt r * s ^ 2 := by
  rw [Real.rpow_add (by positivity), ← Real.sqrt_eq_rpow]
  have h1 : Real.sqrt (16 * n * r * s * s) =
      4 * Real.sqrt n * Real.sqrt r * s := by
    rw [show 16 * n * r * s * s = 16 * n * r * s ^ 2 by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ 16 * n * r), Real.sqrt_sq hs.le,
      Real.sqrt_mul (by positivity : 0 ≤ 16 * n),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  have h2 : Real.sqrt (8 * n * s * s * V) =
      Real.sqrt 8 * Real.sqrt n * s * Real.sqrt V := by
    rw [show 8 * n * s * s * V = 8 * n * s ^ 2 * V by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ 8 * n * s ^ 2),
      Real.sqrt_mul (by positivity : 0 ≤ 8 * n), Real.sqrt_sq hs.le,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
  rw [h1, h2]
  calc
    _ = (8 * Real.sqrt 8) * (16 * n * r * s * s) ^ κ * Real.sqrt V *
        (Real.sqrt n) ^ 2 * r * Real.sqrt r * s ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hn.le]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
