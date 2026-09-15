import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeRectangleUniform
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalContinuousRectangle

namespace Wu2008DoubleSieve
open Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Topology

/-- The finite labelled rectangle approximates the actual weighted Lebesgue integral. -/
theorem primeRectangle_integral_discrepancy {n : ℕ} {R : ℝ}
    (hR : 1 < R) (hs : primeOrderedMertensStart ≤ R ^ (1 / 10 : ℝ))
    (A B : Fin n → ℝ) (hA : ∀ i, 1 / 10 ≤ A i)
    (hAB : ∀ i, A i ≤ B i) (hB : ∀ i, B i ≤ 1 / 2) :
    IntegrableOn continuousDensity (continuousRectangle A B) ∧
      |primeRectangleMass R A B -
        ∫ t in continuousRectangle A B, continuousDensity t| ≤
        (n : ℝ) * primeOrderedDiscrepancy R *
          (4 + primeOrderedDiscrepancy R) ^ (n - 1) := by
  refine ⟨continuousRectangle_integrable A B hA, ?_⟩
  rw [continuousRectangle_factorization A B hAB]
  exact primeRectangle_discrepancy hR hs A B hA hAB hB

/-- Fix dimension and tolerance before the scale and both moving endpoint vectors. -/
theorem primeRectangle_integral_threshold (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ A B : Fin n → ℝ,
      (∀ i, 1 / 10 ≤ A i) → (∀ i, A i ≤ B i) → (∀ i, B i ≤ 1 / 2) →
      IntegrableOn continuousDensity (continuousRectangle A B) ∧
        |primeRectangleMass R A B -
          ∫ t in continuousRectangle A B, continuousDensity t| < ε := by
  obtain ⟨T, hT, h⟩ := primeRectangle_uniform_threshold n ε hε
  refine ⟨T, hT, ?_⟩
  intro R hR A B hA hAB hB
  refine ⟨continuousRectangle_integrable A B hA, ?_⟩
  rw [continuousRectangle_factorization A B hAB]
  exact h R hR A B hA hAB hB

/-- A fixed positive ambient power also preserves the same literal integral. -/
theorem primeRectangle_integral_ambient_threshold (rho : ℝ) (hrho : 0 < rho)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 1 < T ∧ ∀ N : ℝ, T ≤ N → ∀ R : ℝ, N ^ rho ≤ R →
      ∀ A B : Fin n → ℝ,
      (∀ i, 1 / 10 ≤ A i) → (∀ i, A i ≤ B i) → (∀ i, B i ≤ 1 / 2) →
      IntegrableOn continuousDensity (continuousRectangle A B) ∧
        |primeRectangleMass R A B -
          ∫ t in continuousRectangle A B, continuousDensity t| < ε := by
  obtain ⟨T, hT, h⟩ := primeRectangle_ambient_threshold rho hrho n ε hε
  refine ⟨T, hT, ?_⟩
  intro N hN R hR A B hA hAB hB
  refine ⟨continuousRectangle_integrable A B hA, ?_⟩
  rw [continuousRectangle_factorization A B hAB]
  exact h N hN R hR A B hA hAB hB

/-- Both actual zero-dimensional masses equal one, so their discrepancy is zero. -/
theorem primeRectangle_integral_zero (R : ℝ) (A B : Fin 0 → ℝ) :
    |primeRectangleMass R A B -
      ∫ t in continuousRectangle A B, continuousDensity t| = 0 := by
  rw [primeRectangle_zero, continuousRectangle_integral_zero, sub_self, abs_zero]

end Wu2008DoubleSieve
