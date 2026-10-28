import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiErrorEnvelopeCeilBridge
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIEndpointRegime
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigmaElevenPrimeSumIdentification
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigmaTwelveCarrierEquality

open scoped Classical BigOperators
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000


/-- At `s = β+1`, the finite correction in `caseITau` is inactive under the
same explicit large-`D` logarithmic threshold as in Case I. -/
theorem caseITau_eq_beta_add_one_of_log_threshold
    {β D : ℝ} (hβ : 1 < β) (hD : 1 < D)
    (hDlarge : β * Real.log 2 ≤ (β - 1) * Real.log D) :
    caseITau D (β + 1) = β + 1 :=
  caseITau_eq_s_of_log_threshold hβ (by linarith) hD hDlarge


end MathlibNt.SieveTheory
