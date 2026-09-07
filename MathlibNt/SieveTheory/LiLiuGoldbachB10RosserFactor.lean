import MathlibNt.SieveTheory.LiLiuGoldbachB10FibreSieve
import MathlibNt.SieveTheory.MertensTheorem
import MathlibNt.SieveTheory.JurkatRichert1965Section13HatSource
import MathlibNt.SieveTheory.SuzukiClaim145SourceParameters
import MathlibNt.SieveTheory.SuzukiUpperRosserDensityEndpointDirect

open scoped BigOperators

open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem B10RosserFactor_modernUpperDensity :
    DimensionOneUpperRosserDensityFundamentalLemma :=
  MathlibNt.SieveTheory.dimensionOneUpperRosserDensityFundamentalLemma_of_suzuki_allDepth
    jr1965Section13HatLayers jr1965Section13HatSourceContract
    (show MathlibNt.SieveTheory.SuzukiClaim145SourceParameters
        (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) by
      constructor <;> norm_num)

/-- A single Mertens constant works for every finite `B10` pushforward sieve,
because evenness of `N` removes the exceptional prime `2` from the actual
sifting product. -/
theorem exists_goldbachB10BoundingSieve_dimensionOneLocalProductBound :
    ∃ K : ℝ, 1 < K ∧ ∀ (N : ℕ) (hEven : Even N) (ε b c Z X : ℝ),
      HasDimensionOneLocalProductBound
        (goldbachB10BoundingSieve N hEven ε b c Z X) K := by
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N hEven ε b c Z X z₁ z₂ hz₁ hz₁₂
  let s : Finset ℕ :=
    (goldbachB10ProdPrimes N Z).primeFactors.filter
      (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' :
        p ∈ (goldbachB10ProdPrimes N Z).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hpdiv : p ∣ goldbachB10ProdPrimes N Z :=
      (Nat.mem_primeFactors_of_ne_zero
        (goldbachB10ProdPrimes_ne_zero N Z)).mp hp'.1 |>.2
    have hpN : ¬ p ∣ N := (prime_dvd_goldbachB10ProdPrimes_iff hprime).mp hpdiv |>.2
    have hp2 : 2 < p := by
      have hpne : p ≠ 2 := by
        intro hpEq
        apply hpN
        rw [hpEq]
        exact even_iff_two_dvd.mp hEven
      exact lt_of_le_of_ne hprime.two_le (by simpa using hpne.symm)
    exact ⟨hprime, hp2⟩
  have hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
    intro p hp
    have hp' :
        p ∈ (goldbachB10ProdPrimes N Z).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    exact hp'.2
  have hbound := hinterval s hs z₁ z₂ hz₁ hz₁₂ hsinterval
  change (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) ≤
    Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁)
  calc
    (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) =
        ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (hs p hp).1]
    _ ≤ Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) := hbound

private theorem B10RosserFactor_upperRosserWeight_certificate
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
  have hcut : ∀ p ∈ (goldbachB10ProdPrimes N Z).primeFactors, p < Nat.floor Δ + 1 := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ goldbachB10ProdPrimes N Z :=
      (Nat.mem_primeFactors_of_ne_zero
        (goldbachB10ProdPrimes_ne_zero N Z)).mp hp |>.2
    exact lt_floor_add_one_of_le_of_log_ratio
      (p := p) hZ hΔ
      (prime_dvd_goldbachB10ProdPrimes_lt hpPrime hpdvd).le hs hslo
  exact LinearSieve.upperRosserWeight_certificate
    (goldbachB10ProdPrimes_squarefree N Z)
    (goldbachB10ProdPrimes_ne_zero N Z) hD1 hcut

/-- The actual `B10` sifted count is bounded by the genuine Jurkat--Richert
upper Rosser factor, while retaining the exact finite upper remainder sum. -/
theorem goldbachB10SiftedCount_le_rosserFactor_add_upperErrSum
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, ∀ (N : ℕ) (hEven : Even N) (ε b c Z Δ s X : ℝ),
      z₀ ≤ Z → 2 ≤ Z → 0 < Δ →
      s = Real.log Δ / Real.log Z →
      3 / 2 ≤ s → s ≤ 4 → 0 ≤ X →
      let S := goldbachB10BoundingSieve N hEven ε b c Z X
      let P := goldbachB10ProdPrimes N Z
      (goldbachB10SiftedCount N ε b c Z : ℝ) ≤
        X * (jurkatRichertUpperLinearSieveFactor s + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          LinearSieve.upperErrSum S (Nat.floor Δ + 1)
            (LinearSieve.upperRosserWeight P (Nat.floor Δ + 1)) := by
  obtain ⟨K, hK, hlocal⟩ :=
    exists_goldbachB10BoundingSieve_dimensionOneLocalProductBound
  obtain ⟨z₀, hz₀⟩ := B10RosserFactor_modernUpperDensity K ρ hK hρ
  refine ⟨z₀, ?_⟩
  intro N hEven ε b c Z Δ s X hz₀Z hZ hΔ hs hslo hshi hX
  let S := goldbachB10BoundingSieve N hEven ε b c Z X
  let P := goldbachB10ProdPrimes N Z
  let D : ℕ := Nat.floor Δ + 1
  have hcert : LinearSieve.IsUpperRosserCertificate P D :=
    B10RosserFactor_upperRosserWeight_certificate
      (N := N) (Z := Z) (Δ := Δ) (s := s) hZ hΔ hs hslo
  have hprimeCut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ Z := by
    intro p hp
    have hp' : p ∈ (goldbachB10ProdPrimes N Z).primeFactors := by
      simpa [S, P, goldbachB10BoundingSieve] using hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp'
    have hpdvd : p ∣ goldbachB10ProdPrimes N Z :=
      (Nat.mem_primeFactors_of_ne_zero
        (goldbachB10ProdPrimes_ne_zero N Z)).mp hp' |>.2
    exact (prime_dvd_goldbachB10ProdPrimes_lt hpPrime hpdvd).le
  have hsift :
      S.siftedSum ≤
        X * S.mainSum (LinearSieve.upperRosserWeight P D) +
          LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D) := by
    simpa [S, P, D, goldbachB10BoundingSieve] using
      (LinearSieve.siftedSum_le_mainSum_add_upperErrSum_upperRosser
        (S := S) D hcert)
  have hmain :
      S.mainSum (LinearSieve.upperRosserWeight P D) ≤
        (jurkatRichertUpperLinearSieveFactor s + ρ) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    have hmain' :=
      hz₀ S Z Δ s hz₀Z hZ hΔ
        (hlocal N hEven ε b c Z X)
        (by simpa [S, P, goldbachB10BoundingSieve] using hprimeCut)
        hs hslo hshi
    simpa [S, P, D, goldbachB10BoundingSieve] using hmain'
  have hmainX :
      X * S.mainSum (LinearSieve.upperRosserWeight P D) ≤
        X * ((jurkatRichertUpperLinearSieveFactor s + ρ) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) :=
    mul_le_mul_of_nonneg_left hmain hX
  have hfinal :
      S.siftedSum ≤
        X * ((jurkatRichertUpperLinearSieveFactor s + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) +
          LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D) :=
    hsift.trans <| by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add hmainX
          (le_rfl :
            LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D) ≤
              LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight P D))
  rw [goldbachB10BoundingSieve_siftedSum_eq
    (N := N) (hEven := hEven) (ε := ε) (b := b) (c := c) (Z := Z) (X := X)] at hfinal
  simpa [S, P, D, mul_assoc, mul_left_comm, mul_comm] using hfinal

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig