import MathlibNt.SieveTheory.LiLiuGoldbachS1MainScale
import MathlibNt.SieveTheory.LiLiuGoldbachS3Carrier

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Conditioning changes the carrier and its mass, but not the Euler product. -/
theorem goldbachPairLiEuler_product_eq
    (N : ℕ) (hEven : Even N) (ε z : ℝ) (m : ℕ) :
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (goldbachS3BoundingSieve N hEven ε z m) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (goldbachS1BoundingSieve N hEven ε z) := by
  rfl

/-- Exact conversion of the Mertens normalization; no numerical approximation. -/
theorem goldbachPairLiEuler_coefficient :
    2 * Real.exp (-Real.eulerMascheroniConstant) / (4 / 53 : ℝ) =
      53 / (2 * Real.exp Real.eulerMascheroniConstant) := by
  rw [Real.exp_neg]
  ring

/-- A scalar Li-times-Euler estimate, with the genuine strict endpoint and
    the genuine conditioned sieve. No primality or coprimality of `m` is needed. -/
theorem goldbachPairLiEuler_fixed_epsilon_lower
    (ε η : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hη : 0 < η) (hηu : η < 1 - ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
      ∀ m : ℕ,
        (53 / (2 * Real.exp Real.eulerMascheroniConstant) * (1 - ε - η)) *
            (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) ≤
          BombieriVinogradov.trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
              (goldbachS3BoundingSieve N hEven ε ((N : ℝ) ^ (4 / 53 : ℝ)) m) := by
  obtain ⟨N₀, hN₀, h⟩ := goldbachS1_mainMass_mul_product_lower ε η hε hε1 hη hηu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven m
  have hmain := h N hN hEven (4 / 53 : ℝ) (by norm_num)
  rw [goldbachPairLiEuler_product_eq]
  rw [goldbachPairLiEuler_coefficient] at hmain
  simpa only [goldbachS1BoundingSieve, goldbachS1Endpoint, mul_assoc, mul_div_assoc]
    using hmain

/-- Common small-epsilon normalized scalar lower bound. The cutoff for `ε`
    depends only on `ρ`; the eventual cutoff for `N` is independent of `m`. -/
theorem goldbachPairLiEuler_common_small_epsilon_lower
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2 / 15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
          ∀ m : ℕ,
            (53 / (2 * Real.exp Real.eulerMascheroniConstant) - ρ) *
                (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) ≤
              BombieriVinogradov.trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
                AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                  (goldbachS3BoundingSieve N hEven ε ((N : ℝ) ^ (4 / 53 : ℝ)) m) := by
  let K : ℝ := 53 / (2 * Real.exp Real.eulerMascheroniConstant)
  have hK : 0 < K := by dsimp [K]; positivity
  let ε₀ : ℝ := min (2 / 15 : ℝ) (ρ / (4 * K))
  have he0 : 0 < ε₀ := lt_min (by norm_num) (div_pos hρ (by positivity))
  have he0u : ε₀ ≤ (2 / 15 : ℝ) := min_le_left _ _
  have hbudget : ε₀ * (4 * K) ≤ ρ :=
    (le_div_iff₀ (by positivity : 0 < 4 * K)).mp (min_le_right _ _)
  refine ⟨ε₀, he0, he0u, ?_⟩
  intro ε hε hε0
  have hε1 : ε < 1 := by linarith
  have hηu : ε₀ < 1 - ε := by linarith
  obtain ⟨N₀, hN₀, h⟩ :=
    goldbachPairLiEuler_fixed_epsilon_lower ε ε₀ hε hε1 he0 hηu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven m
  have hscale : 0 ≤ SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log (N : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  have hcoeff : K - ρ ≤ K * (1 - ε - ε₀) := by
    nlinarith [mul_pos hK he0, mul_lt_mul_of_pos_left hε0 hK]
  exact (mul_le_mul_of_nonneg_right hcoeff hscale).trans (h N hN hEven m)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
