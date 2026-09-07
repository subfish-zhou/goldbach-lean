import MathlibNt.SieveTheory.LiLiuGoldbachS2SwitchedDistribution
import MathlibNt.SieveTheory.MertensTheorem
import MathlibNt.SieveTheory.JurkatRichert1965Section13HatSource
import MathlibNt.SieveTheory.SuzukiClaim145SourceParameters
import MathlibNt.SieveTheory.SuzukiUpperRosserDensityEndpointDirect

open scoped BigOperators

open Finset
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable local instance instDecidableGoldbachS2RosserFactor (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The actual `S2` switched sieve uses the standard Goldbach Euler product. -/
noncomputable def goldbachS2PrimeProduct (N : ℕ) (Z : ℝ) : ℝ :=
  MertensTheorem.goldbachSieveProduct N (Nat.ceil Z)

theorem goldbachS2PrimeProduct_eq_sieveProductPrimeFactors
    (N : ℕ) (_hEven : Even N) (T Z : ℝ) :
    goldbachS2PrimeProduct N Z =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (goldbachS2SwitchedBoundingSieve N _hEven T Z) := by
  unfold goldbachS2PrimeProduct MertensTheorem.goldbachSieveProduct
  unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors goldbachS2SwitchedBoundingSieve
  rw [goldbachS1ProdPrimes_primeFactors]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
  rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime hpPrime]

private theorem S2RosserFactor_modernUpperDensity :
    DimensionOneUpperRosserDensityFundamentalLemma :=
  MathlibNt.SieveTheory.dimensionOneUpperRosserDensityFundamentalLemma_of_suzuki_allDepth
    jr1965Section13HatLayers jr1965Section13HatSourceContract
    (show MathlibNt.SieveTheory.SuzukiClaim145SourceParameters
        (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) by
      constructor <;> norm_num)

/-- A single Mertens constant controls the genuine switched `S2` bounding sieve,
since its local density and sifting prime product are the same standard Goldbach
ones used elsewhere in the production branch. -/
theorem exists_goldbachS2SwitchedBoundingSieve_dimensionOneLocalProductBound :
    ∃ K : ℝ, 1 < K ∧ ∀ (N : ℕ) (hEven : Even N) (T Z : ℝ),
      HasDimensionOneLocalProductBound
        (goldbachS2SwitchedBoundingSieve N hEven T Z) K := by
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N hEven T Z z₁ z₂ hz₁ hz₁₂
  let s : Finset ℕ :=
    (goldbachS1ProdPrimes N Z).primeFactors.filter
      (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' :
        p ∈ (goldbachS1ProdPrimes N Z).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hpdiv : p ∣ goldbachS1ProdPrimes N Z :=
      (Nat.mem_primeFactors_of_ne_zero
        (goldbachS1ProdPrimes_ne_zero N Z)).mp hp'.1 |>.2
    have hpN : ¬ p ∣ N := (prime_dvd_goldbachS1ProdPrimes_iff hprime).mp hpdiv |>.2
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
        p ∈ (goldbachS1ProdPrimes N Z).primeFactors ∧
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

private theorem S2RosserFactor_upperRosserWeight_certificate
    {N : ℕ} {Z Δ s : ℝ}
    (hZ : 2 ≤ Z) (hΔ : 0 < Δ) (hs : s = Real.log Δ / Real.log Z)
    (hslo : 3 / 2 ≤ s) :
    LinearSieve.IsUpperRosserCertificate
      (goldbachS1ProdPrimes N Z) (Nat.floor Δ + 1) := by
  have hD1 : 1 < Nat.floor Δ + 1 := by
    have htwo : (2 : ℕ) < Nat.floor Δ + 1 :=
      lt_floor_add_one_of_le_of_log_ratio
        (p := 2) hZ hΔ (by simpa using hZ) hs hslo
    omega
  have hcut : ∀ p ∈ (goldbachS1ProdPrimes N Z).primeFactors, p < Nat.floor Δ + 1 := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ goldbachS1ProdPrimes N Z :=
      (Nat.mem_primeFactors_of_ne_zero
        (goldbachS1ProdPrimes_ne_zero N Z)).mp hp |>.2
    exact lt_floor_add_one_of_le_of_log_ratio
      (p := p) hZ hΔ
      (prime_dvd_goldbachS1ProdPrimes_iff hpPrime |>.mp hpdvd |>.1).le hs hslo
  exact LinearSieve.upperRosserWeight_certificate
    (goldbachS1ProdPrimes_squarefree N Z)
    (goldbachS1ProdPrimes_ne_zero N Z) hD1 hcut

/-- The genuine switched `S2` sifted count is controlled by the honest upper
Rosser factor plus the exact finite upper remainder sum. -/
theorem goldbachS2SwitchedSiftedCount_le_rosserFactor_add_upperErrSum
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, ∀ (N : ℕ) (hEven : Even N) (ε Z Δ s : ℝ),
      z₀ ≤ Z → 2 ≤ Z → 0 < Δ →
      s = Real.log Δ / Real.log Z →
      3 / 2 ≤ s → s ≤ 4 →
      let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
      let S := goldbachS2SwitchedBoundingSieve N hEven T Z
      let P := goldbachS1ProdPrimes N Z
      (goldbachS2SwitchedSiftedCount N T Z : ℝ) ≤
        goldbachS2SwitchedMainMass N T *
            (jurkatRichertUpperLinearSieveFactor s + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          LinearSieve.upperErrSum S (Nat.floor Δ + 1)
            (LinearSieve.upperRosserWeight P (Nat.floor Δ + 1)) := by
  obtain ⟨K, hK, hlocal⟩ :=
    exists_goldbachS2SwitchedBoundingSieve_dimensionOneLocalProductBound
  obtain ⟨z₀, hz₀⟩ := S2RosserFactor_modernUpperDensity K ρ hK hρ
  refine ⟨z₀, ?_⟩
  intro N hEven ε Z Δ s hz₀Z hZ hΔ hs hslo hshi
  let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
  let S := goldbachS2SwitchedBoundingSieve N hEven T Z
  let P := goldbachS1ProdPrimes N Z
  let D : ℕ := Nat.floor Δ + 1
  have hcert : LinearSieve.IsUpperRosserCertificate P D :=
    S2RosserFactor_upperRosserWeight_certificate
      (N := N) (Z := Z) (Δ := Δ) (s := s) hZ hΔ hs hslo
  have hcertS : LinearSieve.IsUpperRosserCertificate S.prodPrimes D := by
    simpa [S, P, goldbachS2SwitchedBoundingSieve] using hcert
  have hprimeCut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ Z := by
    intro p hp
    have hp' : p ∈ (goldbachS1ProdPrimes N Z).primeFactors := by
      simpa [S, P, goldbachS2SwitchedBoundingSieve] using hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp'
    have hpdvd : p ∣ goldbachS1ProdPrimes N Z :=
      (Nat.mem_primeFactors_of_ne_zero
        (goldbachS1ProdPrimes_ne_zero N Z)).mp hp' |>.2
    exact (prime_dvd_goldbachS1ProdPrimes_iff hpPrime).mp hpdvd |>.1.le
  have hsift :
      S.siftedSum ≤
        S.totalMass * S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) +
          LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight S.prodPrimes D) := by
    simpa [D] using
      (LinearSieve.siftedSum_le_mainSum_add_upperErrSum_upperRosser
        (S := S) D hcertS)
  have hmain :
      S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
        (jurkatRichertUpperLinearSieveFactor s + ρ) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    have hmain' :=
      hz₀ S Z Δ s hz₀Z hZ hΔ
        (hlocal N hEven T Z)
        (by simpa [S, P, goldbachS2SwitchedBoundingSieve] using hprimeCut)
        hs hslo hshi
    simpa [D] using hmain'
  have hmainScaled :
      S.totalMass * S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
        S.totalMass *
          ((jurkatRichertUpperLinearSieveFactor s + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) :=
    mul_le_mul_of_nonneg_left hmain (goldbachS2SwitchedMainMass_nonneg N T)
  have hfinal :
      S.siftedSum ≤
        S.totalMass *
            ((jurkatRichertUpperLinearSieveFactor s + ρ) *
              AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) +
          LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight S.prodPrimes D) := by
    exact hsift.trans <| by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add hmainScaled
          (le_rfl :
            LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
              LinearSieve.upperErrSum S D (LinearSieve.upperRosserWeight S.prodPrimes D))
  rw [goldbachS2SwitchedBoundingSieve_siftedSum_eq (N := N) (hEven := hEven) (T := T) (Z := Z)] at hfinal
  simpa [S, T, P, D, goldbachS2SwitchedBoundingSieve, mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- For `Z ≤ N^(1/4)`, the Rosser upper remainder is supported inside the
actual coprime switched remainder sum. -/
theorem goldbachS2_upperErrSum_le_remainderModulusSum
    (N : ℕ) (hEven : Even N) (ε Z : ℝ) (Q : ℕ)
    (hN : 1 ≤ N) (hεu : ε < (2 : ℝ) / 15)
    (hZ : Z ≤ (N : ℝ) ^ ((1 : ℝ) / 4)) :
    let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
    let S := goldbachS2SwitchedBoundingSieve N hEven T Z
    LinearSieve.upperErrSum S (Q + 1)
      (LinearSieve.upperRosserWeight S.prodPrimes (Q + 1)) ≤
      ∑ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N),
        |goldbachS2SwitchedRemainder N T d| := by
  let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
  let S := goldbachS2SwitchedBoundingSieve N hEven T Z
  let I := S.prodPrimes.divisors.filter (fun d => d < Q + 1)
  have hdiv {d : ℕ} (hd : d ∈ I) : d ∣ goldbachS1ProdPrimes N Z :=
    (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  have hsub : I ⊆ (Icc 1 Q).filter (fun d => Nat.Coprime d N) := by
    intro d hd
    have hdPos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hdPos, by
          have := (Finset.mem_filter.mp hd).2
          omega⟩,
        goldbachS1_dvd_prodPrimes_coprime_N (hdiv hd)⟩
  change
    (∑ d ∈ I, |LinearSieve.upperRosserWeight S.prodPrimes (Q + 1) d| * |S.rem d|) ≤
      ∑ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N),
        |goldbachS2SwitchedRemainder N T d|
  calc
    _ ≤ ∑ d ∈ I, |S.rem d| := by
      apply Finset.sum_le_sum
      intro d hd
      exact (mul_le_mul_of_nonneg_right
        (LinearSieve.abs_upperRosserWeight_le_one S.prodPrimes (Q + 1) d)
        (abs_nonneg _)).trans_eq (one_mul _)
    _ = ∑ d ∈ I, |goldbachS2SwitchedRemainder N T d| := by
      apply Finset.sum_congr rfl
      intro d hd
      exact congrArg abs <| by
        simpa [S, T] using
          goldbachS2SwitchedBoundingSieve_rem_eq_remainder_of_dvd_prodPrimes
            (N := N) (hEven := hEven) (ε := ε) (Z := Z) (d := d)
            hN hεu hZ (hdiv hd)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)

/-- The genuine switched `S2` sifted count is bounded by the Rosser main term
plus the actual remainder sum on the moduli `d ≤ floor Δ`. -/
theorem goldbachS2SwitchedSiftedCount_le_rosserFactor_add_remainderModulusSum
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, ∀ (N : ℕ) (hEven : Even N) (ε Z Δ s : ℝ),
      z₀ ≤ Z → 2 ≤ Z → 0 < Δ →
      s = Real.log Δ / Real.log Z →
      3 / 2 ≤ s → s ≤ 4 →
      1 ≤ N → ε < (2 : ℝ) / 15 →
      Z ≤ (N : ℝ) ^ ((1 : ℝ) / 4) →
      let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
      let S := goldbachS2SwitchedBoundingSieve N hEven T Z
      (goldbachS2SwitchedSiftedCount N T Z : ℝ) ≤
        goldbachS2SwitchedMainMass N T *
            (jurkatRichertUpperLinearSieveFactor s + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          ∑ d ∈ (Icc 1 (Nat.floor Δ)).filter (fun d => Nat.Coprime d N),
            |goldbachS2SwitchedRemainder N T d| := by
  obtain ⟨z₀, hbase⟩ :=
    goldbachS2SwitchedSiftedCount_le_rosserFactor_add_upperErrSum ρ hρ
  refine ⟨z₀, ?_⟩
  intro N hEven ε Z Δ s hz₀Z hZ hΔ hs hslo hshi hN hεu hZquarter
  let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
  let S := goldbachS2SwitchedBoundingSieve N hEven T Z
  have hrosser :=
    hbase N hEven ε Z Δ s hz₀Z hZ hΔ hs hslo hshi
  have herr :
      LinearSieve.upperErrSum S (Nat.floor Δ + 1)
        (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
        ∑ d ∈ (Icc 1 (Nat.floor Δ)).filter (fun d => Nat.Coprime d N),
          |goldbachS2SwitchedRemainder N T d| := by
    simpa [S, T] using
      goldbachS2_upperErrSum_le_remainderModulusSum
        N hEven ε Z (Nat.floor Δ) hN hεu hZquarter
  calc
    (goldbachS2SwitchedSiftedCount N T Z : ℝ)
      ≤ goldbachS2SwitchedMainMass N T *
            (jurkatRichertUpperLinearSieveFactor s + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          LinearSieve.upperErrSum S (Nat.floor Δ + 1)
            (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) := by
              simpa [S, T, goldbachS2SwitchedBoundingSieve, mul_assoc, mul_left_comm, mul_comm] using hrosser
    _ ≤ goldbachS2SwitchedMainMass N T *
            (jurkatRichertUpperLinearSieveFactor s + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          ∑ d ∈ (Icc 1 (Nat.floor Δ)).filter (fun d => Nat.Coprime d N),
            |goldbachS2SwitchedRemainder N T d| := by
              exact add_le_add le_rfl herr

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig