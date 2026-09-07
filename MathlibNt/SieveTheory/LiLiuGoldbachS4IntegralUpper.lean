import MathlibNt.SieveTheory.LiLiuGoldbachB8LogGridLimit
import MathlibNt.SieveTheory.LiLiuGoldbachS4PairKernelUpper

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Select the mesh after the tolerance and the prime-size threshold after that mesh. -/
theorem goldbachB8PairLogKernel_le_mainIntegral_eventually
    (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachB8PairLogKernel N ≤ goldbachB8MainIntegral + η := by
  obtain ⟨n, hn, hm⟩ := exists_goldbachB8LogGridUpperSum_le_mainIntegral_add
    (η / 2) (by positivity)
  obtain ⟨N₀, hN₀, hN⟩ := goldbachB8PairLogKernel_le_gridUpperSum_eventually
    n hn (η / 2) (by positivity)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN
  have h := hN N hNN
  linarith

/-- The original S4 count has the genuine integral coefficient 8*I8.
All sieve, Li, finite-transfer, grid and prime-size errors are paid. -/
theorem goldbachS4_normalized_upper_integral
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS4 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) ≤
        (8 * goldbachB8MainIntegral + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  have hI := goldbachB8MainIntegral_nonneg
  have hden : 0 < goldbachB8MainIntegral + 10 := by linarith
  let t : ℝ := min (δ / (goldbachB8MainIntegral + 10)) 1
  have ht : 0 < t := lt_min (div_pos hδ hden) zero_lt_one
  have ht1 : t ≤ 1 := min_le_right _ _
  have htd : t * (goldbachB8MainIntegral + 10) ≤ δ :=
    (le_div_iff₀ hden).mp (min_le_left _ _)
  have hcoef : (8 + t) * (goldbachB8MainIntegral + t) + t ≤
      8 * goldbachB8MainIntegral + δ := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht1)]
  obtain ⟨Ns, hNs, hs⟩ := goldbachS4_normalized_upper_pairKernel t ε ht hε hεu
  obtain ⟨Nk, _hNk, hk⟩ := goldbachB8PairLogKernel_le_mainIntegral_eventually t ht
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

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig