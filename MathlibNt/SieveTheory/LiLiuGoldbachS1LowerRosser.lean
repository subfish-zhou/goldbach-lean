import MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier

open scoped BigOperators

open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachS1LowerRosser (P : Prop) : Decidable P :=
  Classical.propDecidable P

private theorem S1LowerRosser_remainderIndex_subset
    {N : ℕ} {z : ℝ} {D Q0 : ℕ}
    (hDQ : D ≤ Q0 + 1) :
    ((goldbachS1ProdPrimes N z).divisors.filter (fun d => d < D)) ⊆ Icc 1 Q0 := by
  intro d hd
  rcases Finset.mem_filter.mp hd with ⟨hdDiv, hdLtD⟩
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hdDiv
  exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hdPos, by omega⟩

private theorem S1LowerRosser_abs_standardError_le_prefix
    {N : ℕ} {ε z : ℝ} {d : ℕ} (hε : 0 ≤ ε)
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    |MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError
        (goldbachS1Endpoint N ε) d (N % d)| ≤
      MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N d := by
  have hmN : goldbachS1Endpoint N ε ≤ N := goldbachS1Endpoint_le N hε
  calc
    |MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError
        (goldbachS1Endpoint N ε) d (N % d)| ≤
        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPMaxError
          (goldbachS1Endpoint N ε) d := by
            exact
              MathlibNt.SieveTheory.BombieriVinogradov.abs_standardPrimeAPError_le_max
                (goldbachS1_mod_mem_unitResidues (N := N) (z := z) hd)
    _ ≤ MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N d := by
          unfold MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError
          exact Finset.le_max'
            ((range (N + 1)).image
              (fun y => MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPMaxError y d))
            _
            (Finset.mem_image.mpr ⟨goldbachS1Endpoint N ε,
              by simpa using Nat.lt_succ_of_le hmN, rfl⟩)

private theorem S1LowerRosser_abs_rem_le_prefix
    {N : ℕ} (hEven : Even N) {ε z : ℝ} (hε : 0 ≤ ε)
    (hm : 2 ≤ goldbachS1Endpoint N ε) {d : ℕ}
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    |(goldbachS1BoundingSieve N hEven ε z).rem d| ≤
      MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N d := by
  rw [goldbachS1BoundingSieve_rem_eq_standardPrimeAPError
    (N := N) (hEven := hEven) (ε := ε) (z := z) hε hm hd]
  exact S1LowerRosser_abs_standardError_le_prefix (N := N) (ε := ε) (z := z) hε hd

theorem goldbachS1BoundingSieve_lowerErrSum_le_prefixSum
    {N : ℕ} (hEven : Even N) {ε z : ℝ} (hε : 0 ≤ ε)
    (hm : 2 ≤ goldbachS1Endpoint N ε) {D Q0 : ℕ}
    (hDQ : D ≤ Q0 + 1) :
    LinearSieve.lowerErrSum (goldbachS1BoundingSieve N hEven ε z) D
        (LinearSieve.lowerRosserWeight (goldbachS1ProdPrimes N z) D) ≤
      ∑ q ∈ Icc 1 Q0,
        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q := by
  let S := goldbachS1BoundingSieve N hEven ε z
  let P := goldbachS1ProdPrimes N z
  have hpoint :
      ∀ d ∈ P.divisors.filter (fun d => d < D),
        |LinearSieve.lowerRosserWeight P D d| * |S.rem d| ≤
          MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N d := by
    intro d hd
    have hdvd : d ∣ P := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hWeight :
        |LinearSieve.lowerRosserWeight P D d| ≤ 1 :=
      LinearSieve.abs_lowerRosserWeight_le_one P D d
    have hrem :
        |S.rem d| ≤
          MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N d := by
      simpa [S, P] using
        S1LowerRosser_abs_rem_le_prefix (N := N) (hEven := hEven)
          (ε := ε) (z := z) hε hm hdvd
    have hremNonneg : 0 ≤ |S.rem d| := abs_nonneg _
    calc
      |LinearSieve.lowerRosserWeight P D d| * |S.rem d| ≤ 1 * |S.rem d| :=
        mul_le_mul_of_nonneg_right hWeight hremNonneg
      _ ≤ 1 * MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N d :=
        mul_le_mul_of_nonneg_left hrem (by norm_num)
      _ = MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N d := by
        ring
  have hsubset :
      P.divisors.filter (fun d => d < D) ⊆ Icc 1 Q0 :=
    S1LowerRosser_remainderIndex_subset (N := N) (z := z) hDQ
  change
    (∑ d ∈ P.divisors.filter (fun d => d < D),
      |LinearSieve.lowerRosserWeight P D d| * |S.rem d|) ≤
      ∑ q ∈ Icc 1 Q0,
        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q
  calc
    ∑ d ∈ P.divisors.filter (fun d => d < D),
        |LinearSieve.lowerRosserWeight P D d| * |S.rem d| ≤
      ∑ d ∈ P.divisors.filter (fun d => d < D),
        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N d := by
          exact Finset.sum_le_sum hpoint
    _ ≤ ∑ q ∈ Icc 1 Q0,
        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
          intro q _ hqNot
          exact MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError_nonneg N q

/-- The genuine finite `S1` carrier satisfies the lower Rosser inequality with
the exact main sum and the honest standard prime-AP prefix remainder. -/
theorem goldbachS1_lowerRosser_mainTerm_sub_prefix_le
    {N : ℕ} {ε z : ℝ} (hε0 : 0 < ε) (_hε1 : ε < 1) (hEven : Even N)
    (hm : 2 ≤ goldbachS1Endpoint N ε) (_hz : 2 ≤ z)
    {D Q0 : ℕ}
    (hprimeD : ∀ p ∈ (goldbachS1ProdPrimes N z).primeFactors, p < D)
    (hDQ : D ≤ Q0 + 1) :
    MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral
        (goldbachS1Endpoint N ε) *
        (∑ d ∈ (goldbachS1ProdPrimes N z).divisors,
          LinearSieve.lowerRosserWeight (goldbachS1ProdPrimes N z) D d /
            Nat.totient d) -
      ∑ q ∈ Icc 1 Q0,
        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q ≤
      (goldbachS1 (goldbachDifferenceCarrier N ε) N z : ℝ) := by
  let S := goldbachS1BoundingSieve N hEven ε z
  let P := goldbachS1ProdPrimes N z
  let μ := LinearSieve.lowerRosserWeight P D
  have hcert : LinearSieve.IsLowerRosserCertificate P D := by
    apply LinearSieve.lowerRosserWeight_certificate
      (goldbachS1ProdPrimes_squarefree N z)
      (goldbachS1ProdPrimes_ne_zero N z)
      hprimeD
  have hfinite :
      S.totalMass * S.mainSum μ - LinearSieve.lowerErrSum S D μ ≤ S.siftedSum := by
    exact LinearSieve.mainSum_sub_lowerErrSum_le_siftedSum D μ hcert
      (LinearSieve.lowerRosserWeight_hasLowerLevelSupport P D)
  have herr :
      LinearSieve.lowerErrSum S D μ ≤
        ∑ q ∈ Icc 1 Q0,
          MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q := by
    simpa [S, P, μ] using
      goldbachS1BoundingSieve_lowerErrSum_le_prefixSum
        (N := N) (hEven := hEven) (ε := ε) (z := z) (le_of_lt hε0) hm hDQ
  have hmainEq :
      MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral
          (goldbachS1Endpoint N ε) *
          (∑ d ∈ P.divisors, μ d / Nat.totient d) =
        S.totalMass * S.mainSum μ := by
    rw [show S.totalMass =
      MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral
        (goldbachS1Endpoint N ε) by rfl]
    rw [show S.mainSum μ =
      ∑ d ∈ P.divisors, μ d / Nat.totient d by
        simpa [S, P] using
          goldbachS1BoundingSieve_mainSum_eq_totientSum
            (N := N) (hEven := hEven) (ε := ε) (z := z) μ]
  calc
    MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral
        (goldbachS1Endpoint N ε) *
        (∑ d ∈ P.divisors, μ d / Nat.totient d) -
      ∑ q ∈ Icc 1 Q0,
        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q ≤
        S.totalMass * S.mainSum μ - LinearSieve.lowerErrSum S D μ := by
          rw [hmainEq]
          linarith
    _ ≤ S.siftedSum := hfinite
    _ = (goldbachS1 (goldbachDifferenceCarrier N ε) N z : ℝ) := by
          simpa [S] using goldbachS1BoundingSieve_siftedSum_eq
            (N := N) (hEven := hEven) (ε := ε) z

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig