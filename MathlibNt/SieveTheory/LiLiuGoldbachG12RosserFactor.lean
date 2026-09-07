import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedSifted
import MathlibNt.SieveTheory.LiLiuGoldbachG11RosserFactor
import MathlibNt.SieveTheory.LiLiuGoldbachG11EulerProduct

open scoped BigOperators
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- The original Goldbach sieve prime product is unchanged. -/
theorem goldbachG12Linked_prodPrimes_eq (N : ℕ) (hEven : Even N) (ε Z X : ℝ) :
    (goldbachG12LinkedBoundingSieve N hEven ε Z X).prodPrimes =
      (goldbachG11LinkedBoundingSieve N hEven ε Z X).prodPrimes := rfl

/-- The entire multiplicative density is unchanged, not just its prime values. -/
theorem goldbachG12Linked_nu_eq (N : ℕ) (hEven : Even N) (ε Z X : ℝ) :
    (goldbachG12LinkedBoundingSieve N hEven ε Z X).nu =
      (goldbachG11LinkedBoundingSieve N hEven ε Z X).nu := rfl

/-- The actual Euler product, with the inherited local factors. -/
theorem goldbachG12Linked_sieveProduct_eq (N : ℕ) (hEven : Even N) (ε Z X : ℝ) :
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
      (goldbachG12LinkedBoundingSieve N hEven ε Z X) = goldbachB10PrimeProduct N Z :=
  (goldbachB10PrimeProduct_eq_sieveProductPrimeFactors N hEven 0 0 0 Z X).symm

/-- Dimension depends on the inherited prime product and nu, not on the mother weights. -/
theorem exists_goldbachG12LinkedBoundingSieve_dimensionOne :
    ∃ K : ℝ, 1 < K ∧ ∀ (N : ℕ) (hEven : Even N) (ε Z X : ℝ),
      HasDimensionOneLocalProductBound (goldbachG12LinkedBoundingSieve N hEven ε Z X) K := by
  obtain ⟨K, hK, hlocal⟩ := exists_goldbachB10BoundingSieve_dimensionOneLocalProductBound
  exact ⟨K, hK, fun N hEven _ε Z X => hlocal N hEven 0 0 0 Z X⟩

theorem goldbachG12Linked_upperRosserCertificate {N : ℕ} {Z Δ s : ℝ}
    (hZ : 2 ≤ Z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log Z) (hslo : 3/2 ≤ s) :
    LinearSieve.IsUpperRosserCertificate (goldbachB10ProdPrimes N Z) (Nat.floor Δ+1) :=
  goldbachG11Linked_upperRosserCertificate hZ hΔ hs hslo

/-- Actual weighted G12 sieve, consuming the already constructed all-depth source.
The precise finite remainder is retained for the common-distribution consumer. -/
theorem goldbachG12LinkedSiftedMass_le_rosserFactor (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, ∀ (N : ℕ) (hEven : Even N) (ε Z Δ s X : ℝ),
      z₀ ≤ Z → 2 ≤ Z → 0 < Δ → s = Real.log Δ/Real.log Z →
      3/2 ≤ s → s ≤ 4 → 0 ≤ X →
      let S := goldbachG12LinkedBoundingSieve N hEven ε Z X
      let P := goldbachB10ProdPrimes N Z
      goldbachG12LinkedSiftedMass N ε Z ≤
        X*(jurkatRichertUpperLinearSieveFactor s+ρ)*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        LinearSieve.upperErrSum S (Nat.floor Δ+1) (LinearSieve.upperRosserWeight P (Nat.floor Δ+1)) := by
  obtain ⟨K, hK, hlocal⟩ := exists_goldbachG12LinkedBoundingSieve_dimensionOne
  have hdensity : DimensionOneUpperRosserDensityFundamentalLemma :=
    MathlibNt.SieveTheory.dimensionOneUpperRosserDensityFundamentalLemma_of_suzuki_allDepth
      jr1965Section13HatLayers jr1965Section13HatSourceContract
      (show MathlibNt.SieveTheory.SuzukiClaim145SourceParameters (16 : ℝ) (1/2 : ℝ) (7 : ℝ) by
        constructor <;> norm_num)
  obtain ⟨z₀, hz₀⟩ := hdensity K ρ hK hρ
  refine ⟨z₀, ?_⟩
  intro N hEven ε Z Δ s X hz hZ hΔ hs hslo hshi hX
  let S := goldbachG12LinkedBoundingSieve N hEven ε Z X
  let P := goldbachB10ProdPrimes N Z
  let D := Nat.floor Δ+1
  have hcert := goldbachG12Linked_upperRosserCertificate (N := N) hZ hΔ hs hslo
  have hprimeCut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ Z := by
    intro p hp
    have hp' : p ∈ P.primeFactors := hp
    have hprime := Nat.prime_of_mem_primeFactors hp'
    have hpdvd := (Nat.mem_primeFactors_of_ne_zero (goldbachB10ProdPrimes_ne_zero N Z)).mp hp' |>.2
    exact (prime_dvd_goldbachB10ProdPrimes_lt hprime hpdvd).le
  have hmain : S.mainSum (LinearSieve.upperRosserWeight P D) ≤
      (jurkatRichertUpperLinearSieveFactor s+ρ)*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S :=
    hz₀ S Z Δ s hz hZ hΔ (hlocal N hEven ε Z X) hprimeCut hs hslo hshi
  have hf := LinearSieve.siftedSum_le_mainSum_add_upperErrSum_upperRosser (S := S) D hcert
  have hf' : goldbachG12LinkedSiftedMass N ε Z ≤
      X*S.mainSum (LinearSieve.upperRosserWeight P D) +
      LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D) := by
    change (goldbachG12LinkedBoundingSieve N hEven ε Z X).siftedSum ≤ _ at hf
    rw [goldbachG12LinkedBoundingSieve_siftedSum] at hf
    exact hf
  have hmx := mul_le_mul_of_nonneg_left hmain hX
  change goldbachG12LinkedSiftedMass N ε Z ≤
    X*(jurkatRichertUpperLinearSieveFactor s+ρ)*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
      LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D)
  nlinarith only [hf', hmx]

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig