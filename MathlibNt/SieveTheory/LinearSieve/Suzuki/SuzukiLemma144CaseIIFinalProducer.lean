module

public import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIRawRoundedFinal
public import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBaseOneSameC
public import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma11Internal
public import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144SigmaTwoZeroKappaOne
public import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144EndpointSourceBoundsFinal

@[expose] public section

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
