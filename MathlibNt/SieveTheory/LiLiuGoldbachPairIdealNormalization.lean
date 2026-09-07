import MathlibNt.SieveTheory.LiLiuGoldbachPairIdealCoordinate
import MathlibNt.SieveTheory.LiLiuGoldbachPairLiEuler
import MathlibNt.SieveTheory.LiLiuGoldbachPairMovingKernel

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open JurkatRichert1965ChenGammaOneQOne BombieriVinogradov

/-- Scalar normalization and coordinate transport on the same composite atom. -/
theorem goldbachPair_ideal_term_normalized (B ρ : ℝ) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hρK : ρ < 53/(2*Real.exp Real.eulerMascheroniConstant)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
        ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (N : ℝ)^(13/33 : ℝ) →
        let S := goldbachS3BoundingSieve N hEven ε ((N : ℝ)^(4/53 : ℝ)) m
        let D := LiuWeight.panModulusCutoff N B / m + 1
        (53/(2*Real.exp Real.eulerMascheroniConstant)-ρ) *
            (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) *
            goldbachPairIdealWeight N (2*ρ) m ≤
          S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
            max 0 (jr1965f (Real.log (D : ℝ)/Real.log ((N : ℝ)^(4/53 : ℝ)))-ρ) := by
  obtain ⟨Nt, hNt, ht⟩ := goldbachPair_ideal_clip_eventually B ρ hB hρ
  obtain ⟨ε₀, hε₀, hε₀u, he⟩ := goldbachPairLiEuler_common_small_epsilon_lower ρ hρ
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Ne, _, hn⟩ := he ε hε hεlt
  refine ⟨max Nt Ne, by omega, ?_⟩
  intro N hN hEven m hm hmu S D
  have hEuler := hn N (by omega) hEven m
  have hclip := ht N (by omega) m hm hmu
  have hM : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg _))
      (sq_nonneg _)
  have hY : 0 ≤ trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S :=
    (mul_nonneg (sub_nonneg.mpr hρK.le) hM).trans hEuler
  have hXV : 0 ≤ S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    change 0 ≤ trueLogarithmicIntegral (goldbachS1Endpoint N ε)/(Nat.totient m : ℝ) * _
    rw [div_mul_eq_mul_div]
    exact div_nonneg hY (Nat.cast_nonneg _)
  have hw : 0 ≤ goldbachPairIdealWeight N (2*ρ) m := by
    unfold goldbachPairIdealWeight
    exact div_nonneg (le_max_left _ _) (Nat.cast_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_right hEuler hw
  calc
    _ ≤ (trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) *
        goldbachPairIdealWeight N (2*ρ) m := hscaled
    _ = S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        max 0 (jr1965f ((1/2-Real.log (m : ℝ)/Real.log (N : ℝ))/(4/53 : ℝ))-2*ρ) := by
      change (_ * _) * (_ / _) = (_ / _) * _ * _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hclip hXV

/-- The threshold is shared by every finite family of admissible products. -/
theorem goldbachPair_ideal_sum_normalized (B ρ : ℝ) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hρK : ρ < 53/(2*Real.exp Real.eulerMascheroniConstant)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
        ∀ T : Finset (ℕ × ℕ),
          (∀ a ∈ T, 0 < a.1*a.2 ∧ ((a.1*a.2 : ℕ) : ℝ) ≤ (N : ℝ)^(13/33 : ℝ)) →
          (53/(2*Real.exp Real.eulerMascheroniConstant)-ρ) *
            (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) *
            goldbachPairIdealSum N (2*ρ) T ≤ goldbachPairMovingMain N hEven ε B ρ T := by
  obtain ⟨ε₀, hε₀, hε₀u, he⟩ := goldbachPair_ideal_term_normalized B ρ hB hρ hρK
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hn⟩ := he ε hε hεlt
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven T hT
  unfold goldbachPairIdealSum goldbachPairMovingMain
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun a ha => hn N hN hEven (a.1*a.2) (hT a ha).1 (hT a ha).2)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
