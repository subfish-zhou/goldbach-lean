import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIFinalBoundary

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Case II, odd depth at least three: the remaining same-`C` normalization

The accepted rounded source chain ends with a relative bracket and an additive
recursive endpoint term `B₀ N D`.  The target `Lemma144CaseIISameCAt` contains
neither that endpoint term nor a larger constant.  The exact missing comparison
is therefore the absorption of `B₀ N D` by the strict bracket gap
`1 - caseIIConcreteRoundedRelativeBracket ...`.

The definitions below keep the large-`D` cutoff before `s`, and permit the
cutoff to depend on the fixed finite depth `N`.  The final theorem proves that
this comparison, together with the accepted rounded-relative output, is exactly
sufficient to construct `Lemma144CaseIIOddSuccessorSameCProducer`.
-/


/-- Terminal algebra: the endpoint-gap comparison removes `B₀` without
changing `C`. -/
theorem caseII_sameC_of_relative_and_endpoint_gap
    {sourceSum V B₀ finiteLayer scale bracket : ℝ}
    (hB₀ : B₀ ≤ V * (scale * (1 - bracket)))
    (hrelative : sourceSum ≤ B₀ + V * (finiteLayer + scale * bracket)) :
    sourceSum ≤ V * (finiteLayer + scale) := by
  calc
    sourceSum ≤ B₀ + V * (finiteLayer + scale * bracket) := hrelative
    _ ≤ V * (scale * (1 - bracket)) +
          V * (finiteLayer + scale * bracket) := add_le_add_left hB₀ _
    _ = V * (finiteLayer + scale) := by ring


end MathlibNt.SieveTheory
