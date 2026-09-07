import MathlibNt.SieveTheory.LiLiuGoldbachG11UniformScalar
import MathlibNt.SieveTheory.LiLiuGoldbachG11SharpBuchstabConsumed

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Actual G11 on the original difference carrier, with the cutoff uniform over
all nonnegative epsilon. This consumes the proved uniform sieve factor 8 and
the real Buchstab bound 561522/1000000; it is not an author-weight estimate. -/
theorem goldbachWeightG11_le_uniformScalar_numeric (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ), 0 ≤ ε →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ) ≤
        ((10385101 / 100000000 : ℝ) + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  obtain ⟨N₀, hN₀, hb⟩ := goldbachWeightG11_le_sharpBuchstabIntegral δ hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven ε hε
  have hm : 0 ≤ SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg _)) (sq_nonneg _)
  have hc : g11UniformScalar + δ ≤ g11UniformScalarUpper + δ := by
    linarith only [g11UniformScalar_lt_upper]
  exact (hb N hN hEven ε hε).trans (mul_le_mul_of_nonneg_right hc hm)

/-- The strict rational upward rounding absorbs a positive asymptotic loss.
Consequently the fixed number itself bounds the actual count eventually,
with N₀ chosen before every epsilon >= 0. -/
theorem goldbachWeightG11_le_uniformScalar_numeric_fixed :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (_hEven : Even N) (ε : ℝ), 0 ≤ ε →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ) ≤
        (10385101 / 100000000 : ℝ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  have hδ : 0 < g11UniformScalarUpper - g11UniformScalar :=
    sub_pos.mpr g11UniformScalar_lt_upper
  obtain ⟨N₀, hN₀, hb⟩ := goldbachWeightG11_le_sharpBuchstabIntegral
    (g11UniformScalarUpper - g11UniformScalar) hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven ε hε
  have h := hb N hN hEven ε hε
  change _ ≤ (g11UniformScalar + (g11UniformScalarUpper - g11UniformScalar)) * _ at h
  have he : g11UniformScalar + (g11UniformScalarUpper - g11UniformScalar) =
      g11UniformScalarUpper := by ring
  rw [he] at h
  exact h

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig