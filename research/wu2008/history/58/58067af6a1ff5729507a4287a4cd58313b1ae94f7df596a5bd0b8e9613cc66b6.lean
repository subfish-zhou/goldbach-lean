import MathlibNt.Wu2008DoubleSieve.Omega3SieveIdentity

/-! Exact local product of the actual labelled switched BoundingSieve. -/

namespace Wu2008DoubleSieve

open Finset
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple

theorem omega3GoldbachBoundingSieve_sieveProduct {i : ℕ} (N : ℕ) (he : Even N)
    (δ s t Z : ℝ) (W : Fin i → Finset ℕ) :
    sieveProductPrimeFactors (omega3GoldbachBoundingSieve N he δ s t Z W) =
      localSieveProduct N Z := by
  change (∏ p ∈ (ordinarySievePrimeProduct N Z).primeFactors,
    (1 - goldbachNu p)) = _
  rw [ordinarySievePrimeProduct_primeFactors, localSieveProduct,
    localSievePrimes_eq_primeWindow]
  apply prod_congr rfl
  intro p hp
  rw [goldbachNu_apply_prime (mem_primeWindow.mp hp).1]

end Wu2008DoubleSieve
