import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Ring.Parity

/-!
# The literal statement of Chen's theorem

This specification uses only natural-number primality, parity, addition, and
multiplication. It does not use any project-specific almost-prime predicate.
The two factors in the composite case are allowed to coincide.
-/

namespace Goldbach

/-- Every sufficiently large even natural number is a prime plus either a prime
or a product of two primes. The threshold is existential, not explicit. -/
def ChenTheorem : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q = r * s) ∧ N = p + q

end Goldbach
