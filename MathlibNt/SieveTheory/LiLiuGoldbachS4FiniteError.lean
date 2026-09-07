import MathlibNt.SieveTheory.LiLiuGoldbachWeightLogScale
import MathlibNt.SieveTheory.LiLiuGoldbachBadBound
import MathlibNt.SieveTheory.LiuSingularSeries

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Pay labelled bad atoms and labelled small prime outputs; this does not
assert the still separate finite S4-to-switched-carrier comparison. -/
theorem goldbachS4_finiteLoss_le_sqrt (N : ℕ) (ε Z : ℝ)
    (hN : 1 ≤ N) (hZ : 0 ≤ Z) (hZu : Z ≤ Real.sqrt (N : ℝ)) :
    400 * (goldbachBadCount (goldbachDifferenceCarrier N ε) N : ℝ) +
      400 * (Nat.floor Z : ℝ) ≤ 1200 * Real.sqrt (N : ℝ) := by
  have hN0 : N ≠ 0 := by omega
  have hb := (goldbachBadCount_le_primeFactors N ε hN0).trans
    (show (N.primeFactors.card : ℤ) ≤ ((N.sqrt + 1 : ℕ) : ℤ) by
      exact_mod_cast goldbach_primeFactors_card_le_sqrt_add_one N hN0)
  have hbR : (goldbachBadCount (goldbachDifferenceCarrier N ε) N : ℝ) ≤
      (N.sqrt : ℝ) + 1 := by exact_mod_cast hb
  have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hns2 : (N.sqrt : ℝ)^2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
  have hns : (N.sqrt : ℝ) ≤ Real.sqrt (N : ℝ) := by
    nlinarith [show (0 : ℝ) ≤ (N.sqrt : ℝ) from Nat.cast_nonneg _]
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by nlinarith
  have hf : (Nat.floor Z : ℝ) ≤ Real.sqrt (N : ℝ) := (Nat.floor_le hZ).trans hZu
  linarith

/-- The threshold is uniform in epsilon and every later moving cutoff Z.
Only the actual finite transfer loss is paid, not the switched sifted count. -/
theorem goldbachS4_finiteLoss_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε Z : ℝ,
      0 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
      400 * (goldbachBadCount (goldbachDifferenceCarrier N ε) N : ℝ) +
        400 * (Nat.floor Z : ℝ) ≤
        δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  obtain ⟨Ne, _hNe, he⟩ := goldbach_power_error_le_log_scale_eventually
    1200 (1 / 2) (δ * SingularSeries.liuUniversalProduct)
    (by norm_num) (by norm_num) (mul_pos hδ SingularSeries.liuUniversalProduct_pos)
  refine ⟨max 4 Ne, le_max_left _ _, ?_⟩
  intro N hN ε Z hZ hZu
  have hN1 : 1 ≤ N := by have := (le_max_left _ _).trans hN; omega
  have hp : 1200 * Real.sqrt (N : ℝ) ≤
      (δ * SingularSeries.liuUniversalProduct) * (N : ℝ) / Real.log (N : ℝ)^2 := by
    convert he N ((le_max_right _ _).trans hN) (1 / 2) le_rfl using 1
    norm_num [Real.sqrt_eq_rpow]
  have hm : 0 ≤ (N : ℝ) / Real.log (N : ℝ)^2 := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hseries := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hδ.le) hm
  calc
    _ ≤ 1200 * Real.sqrt (N : ℝ) := goldbachS4_finiteLoss_le_sqrt N ε Z hN1 hZ hZu
    _ ≤ _ := hp
    _ ≤ _ := by simpa only [div_eq_mul_inv, mul_assoc] using hseries

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig