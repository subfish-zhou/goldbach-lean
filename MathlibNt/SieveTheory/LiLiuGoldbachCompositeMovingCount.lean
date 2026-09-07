import MathlibNt.SieveTheory.LiLiuGoldbachCompositeMovingDensity
import MathlibNt.SieveTheory.LiLiuGoldbachOrderedPairLevel
import MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser

open scoped BigOperators
open Filter Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open BombieriVinogradov JurkatRichert1965ChenGammaOneQOne

private theorem movingCount_li_nonneg {N : ℕ} {ε : ℝ}
    (hN : 4 ≤ N) (hε : ε < (2 : ℝ)/15) :
    0 ≤ trueLogarithmicIntegral (goldbachS1Endpoint N ε) := by
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 3 ≤ (1-ε)*(N : ℝ) := by nlinarith
  have hc : 3 ≤ Nat.ceil ((1-ε)*(N : ℝ)) := by
    exact_mod_cast hx.trans (Nat.le_ceil ((1-ε)*(N : ℝ)))
  have hm : 2 ≤ goldbachS1Endpoint N ε := by unfold goldbachS1Endpoint; omega
  exact LiuWeight.liuLogarithmicIntegral_nonneg (2 / Real.log 2)
    (div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le) (by exact_mod_cast hm)

/-- The actual count on every moving composite layer, including t < 2.
Clipping is justified by count nonnegativity, not signed-density nonnegativity.
The literal Rosser remainder remains available for the proved full BV sum. -/
theorem goldbachComposite_moving_count_lower (B ρ : ℝ) (hB : 0 ≤ B) (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
      ∀ ε : ℝ, ε < 2/15 → ∀ m : ℕ, 0 < m →
        (N : ℝ)^(8/53 : ℝ) ≤ (m : ℝ) →
        (m : ℝ) ≤ (N : ℝ)^(13/33 : ℝ) →
        let S := goldbachS3BoundingSieve N hEven ε ((N : ℝ)^(4/53 : ℝ)) m
        let D := LiuWeight.panModulusCutoff N B / m + 1
        let t := Real.log (D : ℝ) / Real.log ((N : ℝ)^(4/53 : ℝ))
        S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
            max 0 (jr1965f t - ρ) -
          LinearSieve.lowerErrSum S D (LinearSieve.lowerRosserWeight S.prodPrimes D) ≤
        (literalH (goldbachDifferenceCarrier N ε) N m ((N : ℝ)^(4/53 : ℝ)) : ℝ) := by
  obtain ⟨Nc, hNc, hdensity⟩ := goldbachComposite_moving_lowerDensity B ρ hB hρ
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp (goldbachOrderedPair_level_eventually B)
  refine ⟨max Nc Nl, by omega, ?_⟩
  intro N hN hEven ε hε m hm hml hmu S D t
  have hN4 : 4 ≤ N := by omega
  have hX : 0 ≤ S.totalMass :=
    div_nonneg (movingCount_li_nonneg hN4 hε) (Nat.cast_nonneg _)
  have hE : 0 ≤ LinearSieve.lowerErrSum S D
      (LinearSieve.lowerRosserWeight S.prodPrimes D) := by
    unfold LinearSieve.lowerErrSum
    positivity
  by_cases hnonpos : jr1965f t - ρ ≤ 0
  · rw [max_eq_left hnonpos]
    simp only [mul_zero, zero_sub]
    have hcount : 0 ≤ (literalH (goldbachDifferenceCarrier N ε) N m
        ((N : ℝ)^(4/53 : ℝ)) : ℝ) := by
      unfold literalH
      positivity
    exact (neg_nonpos.mpr hE).trans hcount
  · have hpos : 0 < jr1965f t - ρ := lt_of_not_ge hnonpos
    have ht : 2 ≤ t := by
      by_contra hn
      have hf := jr1965f_initial (le_of_lt (lt_of_not_ge hn))
      linarith
    rw [max_eq_right hpos.le]
    have hd := hdensity N (by omega) hEven ε m hm hml hmu ht
    have hprimes : ∀ p ∈ S.prodPrimes.primeFactors, p < D :=
      ((hl N (by omega)).2 m hm hmu).2
    have hcert : LinearSieve.IsLowerRosserCertificate S.prodPrimes D :=
      LinearSieve.lowerRosserWeight_certificate S.prodPrimes_squarefree
        S.prodPrimes_ne_zero hprimes
    have hf := LinearSieve.mainSum_sub_lowerErrSum_le_siftedSum
      (S := S) D (LinearSieve.lowerRosserWeight S.prodPrimes D) hcert
      (LinearSieve.lowerRosserWeight_hasLowerLevelSupport S.prodPrimes D)
    have hmains := mul_le_mul_of_nonneg_left hd hX
    rw [← mul_assoc] at hmains
    have hh := (sub_le_sub_right hmains
      (LinearSieve.lowerErrSum S D (LinearSieve.lowerRosserWeight S.prodPrimes D))).trans hf
    simpa only [goldbachS3BoundingSieve_siftedSum_eq] using hh

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
