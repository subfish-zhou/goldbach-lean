import Goldbach.Statement
import MathlibNt.ChensTheoremUnconditional

/-!
# Chen's theorem

The public theorem is stated in the independent, literal specification from
`Goldbach.Statement`. Its proof supplies the complete sieve and distribution
chain and expands the internal almost-prime predicate.
-/

namespace Goldbach

/-- The unconditional prime-plus-at-most-two-primes theorem. -/
theorem chen_theorem : ChenTheorem := by
  obtain ⟨N₀, h⟩ := MathlibNt.ChensTheorem.chens_theorem_unconditional
  refine ⟨N₀, ?_⟩
  intro N hN hEven
  obtain ⟨p, q, hp, hq, hsum⟩ := h N hN hEven
  exact ⟨p, q, hp, MathlibNt.ChensTheorem.semiprime_iff.mp hq, hsum⟩

/-- The number of actual representations has the stated eventual lower bound.
`liuSingularSeries` is the normalization used throughout the sieve assembly. -/
theorem representation_lower_bound :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (0.67 : ℝ) * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
        Real.log N ^ (2 : ℕ) ≤
      ((MathlibNt.SieveTheory.SwitchingPrinciple.chenGoodRepresentations N).card : ℝ) :=
  MathlibNt.ChensTheorem.chen_good_representations_lower_bound_unconditional

end Goldbach
