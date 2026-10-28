import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingComparison
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The source-faithful κ=1 content of (T5): for each sign, `T̂` is eventually
bounded by a (sign-dependent) constant times `exp (-s)`.  This says decay only;
it does not mention a pairing. -/
def Section13HatExponentialDecay (H : Section13HatLayers) : Prop :=
  ∀ sign, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in atTop, |H.T sign s| ≤ C * Real.exp (-s)


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
