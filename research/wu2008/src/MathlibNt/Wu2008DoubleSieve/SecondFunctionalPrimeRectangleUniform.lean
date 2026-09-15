import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeRectangleProduct

namespace Wu2008DoubleSieve
open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

/-- Dimension is fixed before taking the limit; no uniformity over unbounded n. -/
theorem primeRectangle_error_tendsto (n : ℕ) :
    Tendsto (fun R : ℝ => (n : ℝ) * primeOrderedDiscrepancy R *
      (4 + primeOrderedDiscrepancy R) ^ (n - 1)) atTop (𝓝 0) := by
  have h := (primeOrderedDiscrepancy_tendsto.const_mul (n : ℝ)).mul
    (((tendsto_const_nhds (x := (4 : ℝ))).add primeOrderedDiscrepancy_tendsto).pow (n - 1))
  simpa only [mul_zero, zero_mul, add_zero] using h

/-- All moving endpoint vectors are quantified after the eventual threshold. -/
theorem primeRectangle_uniform (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ A B : Fin n → ℝ,
      (∀ i, 1 / 10 ≤ A i) → (∀ i, A i ≤ B i) → (∀ i, B i ≤ 1 / 2) →
      |primeRectangleMass R A B - ∏ i, ∫ t in A i..B i, 1 / t| < ε := by
  filter_upwards [eventually_gt_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop primeOrderedMertensStart),
    (primeRectangle_error_tendsto n).eventually (gt_mem_nhds hε)] with R hR hs he
  intro A B hA hAB hB
  exact (primeRectangle_discrepancy hR hs A B hA hAB hB).trans_lt he

/-- An actual fixed-n epsilon threshold, independent of both moving vectors. -/
theorem primeRectangle_uniform_threshold (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R0 : ℝ, 1 < R0 ∧ ∀ R : ℝ, R0 ≤ R → ∀ A B : Fin n → ℝ,
      (∀ i, 1 / 10 ≤ A i) → (∀ i, A i ≤ B i) → (∀ i, B i ≤ 1 / 2) →
      |primeRectangleMass R A B - ∏ i, ∫ t in A i..B i, 1 / t| < ε := by
  obtain ⟨R0, hR0⟩ := eventually_atTop.1 (primeRectangle_uniform n ε hε)
  refine ⟨max R0 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro R hR
  exact hR0 R ((le_max_left _ _).trans hR)

/-- Literal four-dimensional reciprocal-prime rectangle consumer. -/
theorem primeRectangle_fin4 {R : ℝ}
    (hR : 1 < R) (hs : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (A B : Fin 4 → ℝ) (hA : ∀ i, 1 / 10 ≤ A i)
    (hAB : ∀ i, A i ≤ B i) (hB : ∀ i, B i ≤ 1 / 2) :
    |(∑ p : Fin 4 → primeSlabPrimes R,
      if ∀ i, log (p i).val / log R ∈ Icc (A i) (B i)
      then ∏ i, 1 / ((p i).val : ℝ) else 0) - ∏ i, ∫ t in A i..B i, 1 / t| ≤
      4 * primeOrderedDiscrepancy R * (4 + primeOrderedDiscrepancy R) ^ 3 := by
  simpa [primeRectangleMass, primeSlabWeight] using
    primeRectangle_discrepancy hR hs A B hA hAB hB

/-- Literal five-dimensional reciprocal-prime rectangle consumer. -/
theorem primeRectangle_fin5 {R : ℝ}
    (hR : 1 < R) (hs : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (A B : Fin 5 → ℝ) (hA : ∀ i, 1 / 10 ≤ A i)
    (hAB : ∀ i, A i ≤ B i) (hB : ∀ i, B i ≤ 1 / 2) :
    |(∑ p : Fin 5 → primeSlabPrimes R,
      if ∀ i, log (p i).val / log R ∈ Icc (A i) (B i)
      then ∏ i, 1 / ((p i).val : ℝ) else 0) - ∏ i, ∫ t in A i..B i, 1 / t| ≤
      5 * primeOrderedDiscrepancy R * (4 + primeOrderedDiscrepancy R) ^ 4 := by
  simpa [primeRectangleMass, primeSlabWeight] using
    primeRectangle_discrepancy hR hs A B hA hAB hB

/-- A common ambient threshold precedes N, every R above N^lambda, and all endpoints. -/
theorem primeRectangle_ambient_threshold (rho : ℝ) (hrho : 0 < rho)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 1 < T ∧ ∀ N : ℝ, T ≤ N → ∀ R : ℝ, N ^ rho ≤ R →
      ∀ A B : Fin n → ℝ,
      (∀ i, 1 / 10 ≤ A i) → (∀ i, A i ≤ B i) → (∀ i, B i ≤ 1 / 2) →
      |primeRectangleMass R A B - ∏ i, ∫ t in A i..B i, 1 / t| < ε := by
  obtain ⟨R0, _, hR0⟩ := primeRectangle_uniform_threshold n ε hε
  obtain ⟨T0, hT0⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop hrho).eventually (eventually_ge_atTop R0))
  refine ⟨max T0 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro N hN R hR
  exact hR0 R ((hT0 N ((le_max_left _ _).trans hN)).trans hR)

end Wu2008DoubleSieve

