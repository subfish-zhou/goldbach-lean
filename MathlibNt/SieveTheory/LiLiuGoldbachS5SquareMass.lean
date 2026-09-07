import MathlibNt.SieveTheory.LiLiuGoldbachErrorFoundations
import MathlibNt.SieveTheory.LiLiuGoldbachS4FiniteError

open Filter
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Pay the actual square mass uniformly over finite carriers below N.
No primality or squarefreeness of the carrier is assumed. -/
theorem goldbachS5_squareMass_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ,
      (∀ n ∈ A, 1 ≤ n ∧ n < N) →
      400 * (goldbachQA A N ((N : ℝ) ^ (4 / 53 : ℝ)) : ℝ) ≤
        δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  have hgrow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 53)).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨Ng, hg⟩ := eventually_atTop.mp (hgrow.eventually (eventually_ge_atTop 2))
  obtain ⟨Ne, _hNe, he⟩ := goldbach_power_error_le_log_scale_eventually
    800 (4 / 53) (δ * SingularSeries.liuUniversalProduct)
    (by norm_num) (by norm_num) (mul_pos hδ SingularSeries.liuUniversalProduct_pos)
  refine ⟨max 4 (max Ng Ne), le_max_left _ _, ?_⟩
  intro N hN A hA
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNg : Ng ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNe : Ne ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hqa := mul_le_mul_of_nonneg_left
    (goldbachQA_real_le_two_mul_div A N _ hA (hg N hNg))
    (by norm_num : (0 : ℝ) ≤ 400)
  have heq : 400 * (2 * (N : ℝ) / (N : ℝ) ^ (4 / 53 : ℝ)) =
      800 * (N : ℝ) ^ (1 - (4 / 53 : ℝ)) := by
    rw [Real.rpow_sub hN0, Real.rpow_one]
    ring
  dsimp only [Function.comp_apply] at hqa
  rw [heq] at hqa
  have hp := he N hNe (4 / 53) le_rfl
  have hm : 0 ≤ (N : ℝ) / Real.log (N : ℝ)^2 :=
    div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hseries := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hδ.le) hm
  exact hqa.trans (hp.trans (by simpa only [div_eq_mul_inv, mul_assoc] using hseries))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig