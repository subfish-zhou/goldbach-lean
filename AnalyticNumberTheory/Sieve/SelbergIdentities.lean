import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Generic Selberg main-term identities

Identities for the Selberg terms of an arbitrary `BoundingSieve`: the prime
value of `g`, and the closed factorization of the divisor sum
`Σ_{d | P} g(d) = ∏_{p | P} (1 - ν(p))⁻¹` over the squarefree sifting
product.  These are the finite algebraic core of the Selberg main term,
shared by every Goldbach-type sieve problem.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real

/-- The Selberg term of any `BoundingSieve` at a prime is
`ν(p) · (1 - ν(p))⁻¹`. -/
theorem selbergTerm_prime {S : BoundingSieve} {p : ℕ} (hp : p.Prime) :
    S.selbergTerms p = S.nu p * (1 - S.nu p)⁻¹ := by
  rw [BoundingSieve.selbergTerms_apply, Nat.Prime.primeFactors hp]
  simp


end AnalyticNumberTheory.Sieve
