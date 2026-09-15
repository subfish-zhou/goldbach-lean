import MathlibNt.Wu2004MeanValue.IndexedSieve
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserDensityEndpointDirect

/-! A finite upper Rosser sieve on the actual indexed sequence.
The real level is `Q / 2`, the prime cutoff is `sqrt Q`, and the genuine
logarithmic ratio is retained. All analytic certificates are constructed. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SwitchingPrinciple
open AnalyticNumberTheory.Sieve
noncomputable section

theorem indexedBoundingSieve_product (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ))
    (z X : ℝ) (hN : Even N) :
    sieveProductPrimeFactors (indexedBoundingSieve N T z X hN) =
      ∏ p ∈ siftingPrimes N z, (1 - 1 / ((p : ℝ) - 1)) := by
  change (∏ p ∈ (siftingProduct N z).primeFactors, (1 - goldbachNu p)) = _
  rw [siftingProduct_primeFactors]
  apply prod_congr rfl
  intro p hp
  rw [goldbachNu_apply_prime (mem_siftingPrimes.mp hp).2.1]

theorem exists_indexedBoundingSieve_dimensionOne :
    ∃ K : ℝ, 1 < K ∧ ∀ (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ))
      (z X : ℝ) (hN : Even N),
      HasDimensionOneLocalProductBound (indexedBoundingSieve N T z X hN) K := by
  obtain ⟨K, hK, hbound⟩ := MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N T z X hN z₁ z₂ hz₁ hz₁₂
  let s := (siftingProduct N z).primeFactors.filter
    (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' := (mem_filter.mp hp).1
    have hprime := Nat.prime_of_mem_primeFactors hp'
    exact ⟨hprime, prime_gt_two_of_dvd_siftingProduct hN hprime
      (Nat.dvd_of_mem_primeFactors hp')⟩
  have h := hbound s hs z₁ z₂ hz₁ hz₁₂ (fun _ hp => (mem_filter.mp hp).2)
  change (∏ p ∈ s, (1 - goldbachNu p)⁻¹) ≤ _
  convert h using 1
  apply prod_congr rfl
  intro p hp
  rw [goldbachNu_apply_prime (hs p hp).1]

theorem sqrt_le_half_of_four_le {Q : ℝ} (hQ : 4 ≤ Q) :
    Real.sqrt Q ≤ Q / 2 := by
  have hQ0 : 0 ≤ Q := by linarith
  have hs := Real.sq_sqrt hQ0
  have hs0 := Real.sqrt_nonneg Q
  nlinarith [sq_nonneg (Real.sqrt Q - 2)]

theorem rosser_halfLevel_support {N d : ℕ} {Q : ℝ} (hQ : 4 ≤ Q)
    (hd : d ∣ siftingProduct N (Real.sqrt Q)) (hlevel : d < ⌊Q / 2⌋₊ + 1) :
    d ∈ sieveDivisors N Q := by
  apply mem_sieveDivisors.mpr
  refine ⟨Nat.pos_of_dvd_of_pos hd (siftingProduct_pos N _), ?_, hd⟩
  have hdf : d ≤ ⌊Q / 2⌋₊ := by omega
  have hhalf : (d : ℝ) ≤ Q / 2 :=
    (Nat.cast_le.mpr hdf).trans (Nat.floor_le (by linarith))
  linarith

theorem indexed_upperRosser_certificate (N : ℕ) {Q : ℝ} (hQ : 4 ≤ Q) :
    IsUpperRosserCertificate (siftingProduct N (Real.sqrt Q)) (⌊Q / 2⌋₊ + 1) := by
  apply upperRosserWeight_certificate (siftingProduct_squarefree N _)
    (siftingProduct_ne_zero N _)
  · have : 2 ≤ ⌊Q / 2⌋₊ := Nat.le_floor (by linarith)
    omega
  · intro p hp
    have hcut := ((prime_dvd_siftingProduct_iff
      (Nat.prime_of_mem_primeFactors hp)).mp (Nat.dvd_of_mem_primeFactors hp)).1
    have hpD : (p : ℝ) < ((⌊Q / 2⌋₊ + 1 : ℕ) : ℝ) := calc
        (p : ℝ) < Real.sqrt Q := hcut
        _ ≤ Q / 2 := sqrt_le_half_of_four_le hQ
        _ < (⌊Q / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        _ = ((⌊Q / 2⌋₊ + 1 : ℕ) : ℝ) := by norm_cast
    exact_mod_cast hpD

theorem indexed_upperRosser_error_le (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ))
    (X Q : ℝ) (hN : Even N) (hQ : 4 ≤ Q) :
    upperErrSum (indexedBoundingSieve N T (Real.sqrt Q) X hN) (⌊Q / 2⌋₊ + 1)
        (upperRosserWeight (siftingProduct N (Real.sqrt Q)) (⌊Q / 2⌋₊ + 1)) ≤
      ∑ d ∈ sieveDivisors N Q, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
        |(indexedDivisibleCount N T d : ℝ) - X / d.totient| := by
  let U := (siftingProduct N (Real.sqrt Q)).divisors.filter
    (fun d => d < ⌊Q / 2⌋₊ + 1)
  have hsub : U ⊆ sieveDivisors N Q := by
    intro d hd
    exact rosser_halfLevel_support hQ (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
      (mem_filter.mp hd).2
  change (∑ d ∈ U, _ * _) ≤ _
  calc
    _ ≤ ∑ d ∈ U, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
        |(indexedDivisibleCount N T d : ℝ) - X / d.totient| := by
      apply sum_le_sum
      intro d hd
      have hdiv := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
      have hsq : (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (sieveDivisors_squarefree (hsub hd))
      rw [indexedBoundingSieve_rem N T _ X hN hdiv, hsq, one_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_upperRosserWeight_le_one _ _ _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _))

theorem indexedSiftedCount_le_rosser_main_add_error (N : ℕ)
    (T : Finset (Σ _ : ℕ, ℕ)) (X Q : ℝ) (hN : Even N) (hQ : 4 ≤ Q) :
    (indexedSiftedCount N T (Real.sqrt Q) : ℝ) ≤
      X * (∑ d ∈ (siftingProduct N (Real.sqrt Q)).divisors,
        upperRosserWeight (siftingProduct N (Real.sqrt Q)) (⌊Q / 2⌋₊ + 1) d /
          d.totient) +
      ∑ d ∈ sieveDivisors N Q, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
        |(indexedDivisibleCount N T d : ℝ) - X / d.totient| := by
  have h := siftedSum_le_mainSum_add_upperErrSum_upperRosser
    (S := indexedBoundingSieve N T (Real.sqrt Q) X hN) (⌊Q / 2⌋₊ + 1)
    (indexed_upperRosser_certificate N hQ)
  rw [indexedBoundingSieve_siftedSum, indexedBoundingSieve_mainSum] at h
  exact h.trans (add_le_add le_rfl (indexed_upperRosser_error_le N T X Q hN hQ))

theorem indexed_upperDensityFundamentalLemma :
    DimensionOneUpperRosserDensityFundamentalLemma := by
  open JurkatRichert1965ChenGammaOneQOne
    SwitchingPrinciple.SuzukiLemma144KappaOne in
    exact dimensionOneUpperRosserDensityFundamentalLemma_of_suzuki_allDepth
      jr1965Section13HatLayers jr1965Section13HatSourceContract
      (show SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) by
        constructor <;> norm_num)

/-- Constants precede the sequence and mass. The error is the literal indexed
common-X remainder; even `N = 0` and zero-valued indices are permitted. -/
theorem indexedSiftedCount_upper_rosser (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧ ∀ (N : ℕ) (T : Finset (Σ _ : ℕ, ℕ)) (X Q : ℝ),
      Even N → 0 ≤ X → 4 ≤ Q → z₀ ≤ Real.sqrt Q →
      3 / 2 ≤ Real.log (Q / 2) / Real.log (Real.sqrt Q) →
      Real.log (Q / 2) / Real.log (Real.sqrt Q) ≤ 4 →
      (indexedSiftedCount N T (Real.sqrt Q) : ℝ) ≤
        X * (∏ p ∈ siftingPrimes N (Real.sqrt Q), (1 - 1 / ((p : ℝ) - 1))) *
          (jurkatRichertUpperLinearSieveFactor
            (Real.log (Q / 2) / Real.log (Real.sqrt Q)) + ρ) +
        ∑ d ∈ sieveDivisors N Q, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
          |(indexedDivisibleCount N T d : ℝ) - X / d.totient| := by
  obtain ⟨K, hK, hlocal⟩ := exists_indexedBoundingSieve_dimensionOne
  obtain ⟨z₀, hbound⟩ := indexed_upperDensityFundamentalLemma K ρ hK hρ
  refine ⟨max 2 z₀, le_max_left _ _, ?_⟩
  intro N T X Q hN hX hQ hz hslo hshi
  have hmain := hbound (indexedBoundingSieve N T (Real.sqrt Q) X hN)
    (Real.sqrt Q) (Q / 2) (Real.log (Q / 2) / Real.log (Real.sqrt Q))
    ((le_max_right _ _).trans hz) ((le_max_left _ _).trans hz)
    (by linarith) (hlocal N T (Real.sqrt Q) X hN)
    (fun p hp => ((prime_dvd_siftingProduct_iff
      (Nat.prime_of_mem_primeFactors hp)).mp (Nat.dvd_of_mem_primeFactors hp)).1.le)
    rfl hslo hshi
  rw [indexedBoundingSieve_product, indexedBoundingSieve_mainSum] at hmain
  have hfinite := indexedSiftedCount_le_rosser_main_add_error N T X Q hN hQ
  calc
    _ ≤ _ := hfinite
    _ ≤ _ := by
      have hmul := mul_le_mul_of_nonneg_left hmain hX
      apply add_le_add _ le_rfl
      simpa only [indexedBoundingSieve, mul_assoc, mul_left_comm, mul_comm] using hmul

end
end Wu2004MeanValue
