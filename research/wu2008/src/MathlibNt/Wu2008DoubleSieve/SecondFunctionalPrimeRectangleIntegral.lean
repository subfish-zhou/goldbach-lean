import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeRectangleUniform
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalContinuousRectangle

namespace Wu2008DoubleSieve
open Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Topology


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



end Wu2008DoubleSieve
