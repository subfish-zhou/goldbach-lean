import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIRawRoundedFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBaseOneSameC
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma11Internal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144SigmaTwoZeroKappaOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144EndpointSourceBoundsFinal

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 3000000

/-- The Case-II side used by the finite-depth partition: odd depth and the
closed low strip.  At even depth this side is empty. -/
def Lemma144CaseIIFinalSide (N : ℕ) (s : ℝ) : Prop :=
  Odd N ∧ s ≤ 3


end MathlibNt.SieveTheory
