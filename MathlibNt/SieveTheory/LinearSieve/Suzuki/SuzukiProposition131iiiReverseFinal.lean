import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1028ReverseEnvelope

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Proposition 13.1(iii), reverse adjacent-ratio direction, with the residual
Lemma-10.28 envelope premise discharged internally from the Section-13 source
contract.  One constant works for both signs and all `2 ≤ s ≤ σ`. -/
theorem proposition131iii_uniform_reverse_adjacent_ratio_of_source
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (sign : ErrorSign) (s σ : ℝ),
      2 ≤ s → s ≤ σ →
      proposition131iiiReverseRatio H sign s ≤
        C * (σ * Real.log (Real.exp 1 * σ)) := by
  exact proposition131iii_uniform_reverse_adjacent_ratio hH
    (section13Qhat_reverseEnvelopeEdge hH)


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
