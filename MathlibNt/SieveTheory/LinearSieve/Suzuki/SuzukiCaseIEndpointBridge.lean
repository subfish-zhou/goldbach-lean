import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseII
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection14LegalDomainBridge

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- A natural ceiling is exactly the natural cutoff representing the strict real
inequality `p < y`. -/
theorem suzukiSupportedBelow_ceil_real
    (S : BoundingSieve) (y : ℝ) :
    suzukiSupportedBelow S ⌈y⌉₊ =
      S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < y) := by
  ext p
  simp [suzukiSupportedBelow, Nat.lt_ceil]


namespace SwitchingPrinciple.SuzukiLemma144KappaOne

open SuzukiFiniteContinuousLayers


end SwitchingPrinciple.SuzukiLemma144KappaOne
end MathlibNt.SieveTheory
