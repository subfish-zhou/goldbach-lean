import MathlibNt.SieveTheory.LiLiuGoldbachB9LogGridLimit
import MathlibNt.SieveTheory.LiLiuGoldbachS5PairKernelUpper
import MathlibNt.SieveTheory.LiLiuGoldbachB9InnerIntegral

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The original S5Closed count has the coarse integral coefficient 8*I9; not the improved low-r coefficient.
All sieve, Li, finite-transfer, grid and prime-size errors are paid. -/
theorem goldbachS5Closed_normalized_upper_integral
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        (8 * goldbachB9MainIntegral + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  have hI := goldbachB9MainIntegral_nonneg
  have hden : 0 < goldbachB9MainIntegral + 10 := by linarith
  let t : ℝ := min (δ / (goldbachB9MainIntegral + 10)) 1
  have ht : 0 < t := lt_min (div_pos hδ hden) zero_lt_one
  have ht1 : t ≤ 1 := min_le_right _ _
  have htd : t * (goldbachB9MainIntegral + 10) ≤ δ :=
    (le_div_iff₀ hden).mp (min_le_left _ _)
  have hcoef : (8 + t) * (goldbachB9MainIntegral + t) + t ≤
      8 * goldbachB9MainIntegral + δ := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht1)]
  obtain ⟨Ns, hNs, hs⟩ := goldbachS5Closed_normalized_upper_pairKernel t ε ht hε hεu
  obtain ⟨Nk, _hNk, hk⟩ := goldbachB9PairLogKernel_le_mainIntegral_eventually t ht
  refine ⟨max Ns Nk, hNs.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hS := hs N ((le_max_left _ _).trans hN) hEven
  have hK := hk N ((le_max_right _ _).trans hN)
  have hscale : 0 ≤ SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  have hpoint := add_le_add (mul_le_mul_of_nonneg_left hK
    (show 0 ≤ 8 + t by positivity)) (le_rfl : t ≤ t)
  exact hS.trans (mul_le_mul_of_nonneg_right (hpoint.trans hcoef) hscale)

theorem goldbachB9MainIntegral_eq_singleIntegral :
    goldbachB9MainIntegral =
      ∫ u in (4 / 53 : ℝ)..(1 / 3), Real.log (2 - 3 * u) / (u * (1 - u)) :=
  goldbachB9DoubleIntegral_eq_singleIntegral

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig