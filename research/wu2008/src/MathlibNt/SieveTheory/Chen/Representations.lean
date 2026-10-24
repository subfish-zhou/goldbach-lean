import Mathlib.NumberTheory.AlmostPrime
import Mathlib.Data.Finset.Range

/-!
# The finite Chen representation set

This count depends only on primality and the number of prime factors. Keeping
it separate from sieve weights lets finite counting arguments use it directly.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open scoped Classical

/-- Prime candidates already satisfying the conclusion of Chen's theorem. -/
noncomputable def chenGoodRepresentations (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p =>
    p.Prime ∧ 2 ≤ N - p ∧ Nat.IsAtMostAlmostPrime 2 (N - p))

end MathlibNt.SieveTheory.SwitchingPrinciple
