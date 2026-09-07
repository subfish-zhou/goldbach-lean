import MathlibNt.SieveTheory.LiLiuGoldbachB8FibreSieve
import MathlibNt.SieveTheory.MertensTheorem
import MathlibNt.SieveTheory.JurkatRichert1965Section13HatSource
import MathlibNt.SieveTheory.SuzukiClaim145SourceParameters
import MathlibNt.SieveTheory.SuzukiUpperRosserDensityEndpointDirect

open scoped BigOperators
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem B8RosserFactor_modernUpperDensity :
    DimensionOneUpperRosserDensityFundamentalLemma :=
  MathlibNt.SieveTheory.dimensionOneUpperRosserDensityFundamentalLemma_of_suzuki_allDepth
    jr1965Section13HatLayers jr1965Section13HatSourceContract
    (show MathlibNt.SieveTheory.SuzukiClaim145SourceParameters
        (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) by
      constructor <;> norm_num)

/-- The local product uses only prime values of the reciprocal-totient density. -/
theorem exists_goldbachB8PlusBoundingSieve_dimensionOneLocalProductBound :
    ∃ K : ℝ, 1 < K ∧ ∀ (N : ℕ) (hEven : Even N) (Z : ℝ),
      HasDimensionOneLocalProductBound (goldbachB8PlusBoundingSieve N hEven Z) K := by
  classical
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N hEven Z z₁ z₂ hz₁ hz₁₂
  let t : Finset ℕ :=
    (goldbachB10ProdPrimes N Z).primeFactors.filter
      (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
  have ht : ∀ p ∈ t, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' :
        p ∈ (goldbachB10ProdPrimes N Z).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [t] using hp
    have hprime := Nat.prime_of_mem_primeFactors hp'.1
    have hpdiv : p ∣ goldbachB10ProdPrimes N Z :=
      (Nat.mem_primeFactors_of_ne_zero
        (goldbachB10ProdPrimes_ne_zero N Z)).mp hp'.1 |>.2
    have hpN := (prime_dvd_goldbachB10ProdPrimes_iff hprime).mp hpdiv |>.2
    have hpne : p ≠ 2 := by
      intro heq
      exact hpN (heq ▸ even_iff_two_dvd.mp hEven)
    exact ⟨hprime, lt_of_le_of_ne hprime.two_le (Ne.symm hpne)⟩
  have htinterval : ∀ p ∈ t, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hbound := hinterval t ht z₁ z₂ hz₁ hz₁₂ htinterval
  change (∏ p ∈ t, (1 - goldbachB8PlusNu p)⁻¹) ≤
    Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁)
  calc
    _ = ∏ p ∈ t, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [goldbachB8PlusNu_eq_goldbachNu_of_squarefree (ht p hp).1.squarefree,
        goldbachNu_apply_prime (ht p hp).1]
    _ ≤ _ := hbound

theorem goldbachB8Plus_upperRosserWeight_certificate
    {N : ℕ} {Z Δ s : ℝ}
    (hZ : 2 ≤ Z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log Z)
    (hslo : 3 / 2 ≤ s) :
    LinearSieve.IsUpperRosserCertificate
      (goldbachB10ProdPrimes N Z) (Nat.floor Δ + 1) := by
  have hD1 : 1 < Nat.floor Δ + 1 := by
    have htwo : (2 : ℕ) < Nat.floor Δ + 1 :=
      lt_floor_add_one_of_le_of_log_ratio
        (p := 2) hZ hΔ (by simpa using hZ) hs hslo
    omega
  have hcut : ∀ p ∈ (goldbachB10ProdPrimes N Z).primeFactors,
      p < Nat.floor Δ + 1 := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ goldbachB10ProdPrimes N Z :=
      (Nat.mem_primeFactors_of_ne_zero
        (goldbachB10ProdPrimes_ne_zero N Z)).mp hp |>.2
    exact lt_floor_add_one_of_le_of_log_ratio
      (p := p) hZ hΔ (prime_dvd_goldbachB10ProdPrimes_lt hpPrime hpdvd).le hs hslo
  exact LinearSieve.upperRosserWeight_certificate
    (goldbachB10ProdPrimes_squarefree N Z)
    (goldbachB10ProdPrimes_ne_zero N Z) hD1 hcut

/-- The genuine upper factor for the full labelled B8plus count and its fixed mass. -/
theorem goldbachB8PlusSiftedCount_le_rosserFactor_add_upperErrSum
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, ∀ (N : ℕ) (hEven : Even N) (Z Δ s : ℝ),
      z₀ ≤ Z → 2 ≤ Z → 0 < Δ →
      s = Real.log Δ / Real.log Z → 3 / 2 ≤ s → s ≤ 4 →
      let S := goldbachB8PlusBoundingSieve N hEven Z
      ((goldbachB8PlusSiftedAtoms N Z).card : ℝ) ≤
        goldbachB8PlusMainMass N * (jurkatRichertUpperLinearSieveFactor s + ρ) *
            sieveProductPrimeFactors S +
          LinearSieve.upperErrSum S (Nat.floor Δ + 1)
            (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) := by
  obtain ⟨K, hK, hlocal⟩ :=
    exists_goldbachB8PlusBoundingSieve_dimensionOneLocalProductBound
  obtain ⟨z₀, hz₀⟩ := B8RosserFactor_modernUpperDensity K ρ hK hρ
  refine ⟨z₀, ?_⟩
  intro N hEven Z Δ s hz₀Z hZ hΔ hs hslo hshi
  let S := goldbachB8PlusBoundingSieve N hEven Z
  let D : ℕ := Nat.floor Δ + 1
  have hcert : LinearSieve.IsUpperRosserCertificate S.prodPrimes D :=
    goldbachB8Plus_upperRosserWeight_certificate hZ hΔ hs hslo
  have hprimeCut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ Z := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ goldbachB10ProdPrimes N Z :=
      (Nat.mem_primeFactors_of_ne_zero
        (goldbachB10ProdPrimes_ne_zero N Z)).mp hp |>.2
    exact (prime_dvd_goldbachB10ProdPrimes_lt hpPrime hpdvd).le
  have hsift :
      S.siftedSum ≤
        goldbachB8PlusMainMass N *
            S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) +
          LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight S.prodPrimes D) :=
    LinearSieve.siftedSum_le_mainSum_add_upperErrSum_upperRosser (S := S) D hcert
  have hmain :
      S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
        (jurkatRichertUpperLinearSieveFactor s + ρ) * sieveProductPrimeFactors S :=
    hz₀ S Z Δ s hz₀Z hZ hΔ (hlocal N hEven Z) hprimeCut hs hslo hshi
  have hmainX := mul_le_mul_of_nonneg_left hmain (goldbachB8PlusMainMass_nonneg N)
  have hfinal := hsift.trans (add_le_add hmainX
    (le_rfl : LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight S.prodPrimes D) ≤ _))
  rw [goldbachB8PlusBoundingSieve_siftedSum_eq_card] at hfinal
  simpa only [mul_assoc] using hfinal

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig