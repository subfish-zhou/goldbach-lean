import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1053NonCircular

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

/-!
# Equation (10.53): source-correct first-crossing reduction

This file corrects the endpoint orientation of the minus first-crossing window.
It proves the pairing-to-kernel inequality with the left endpoint `s-1`, and
records the unique earliest scalar inequality still needed for the strict
(10.56) contradiction.  No stationary exclusion or strict kernel bound is a
record field or theorem premise.
-/

namespace Section10Equation1053KernelExpansion

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10Equation1053
open Section10Equation1053NonCircular


/-- The exact scalar ratio occurring after the source-correct pairing step.
At stationarity its prefactor is the `(10.45)` quantity
`A = ξ(s)-c-2/s`; proving this ratio `< 1` is precisely the first unresolved
scalar inequality.  It is declared as an object, not assumed by any record. -/
noncomputable def equation1056ScalarRatio
    (ξ : ℝ → ℝ) (c s : ℝ) : ℝ :=
  (ξ s - c - 2 / s) *
    (∫ t in s - 1..s,
      Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t)) /
    Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c (s - 1))

/-- Unique earliest scalar frontier left by the source audit.  A complete
internalization of (10.47)--(10.53) must prove this at a sufficiently large
explicit `c` and cutoff, from canonical ξ bounds and the explicit rational
adjoint estimates. -/
def Equation1053EarliestScalarInequality (ξ : ℝ → ℝ) (c s : ℝ) : Prop :=
  equation1056ScalarRatio ξ c s < 1


end Section10Equation1053KernelExpansion
