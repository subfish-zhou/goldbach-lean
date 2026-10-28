import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointQuantitative

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The Claim-14.6(iii) integral contribution in the transported Case-II
endpoint.  It is kept separate from all finite endpoint corrections. -/
noncomputable def caseIIPositiveDeltaIntegralPart
    (H : Section13HatLayers) (N : ℕ)
    (D y d Δ σ C K s : ℝ) : ℝ :=
  (3 / s) * (1 + K / Real.log y) *
    (C * Real.exp (Real.sqrt K) * (Real.log D) ^ (-Δ) *
      ((1 / 3) * (∫ t in (3 : ℝ)..σ,
        qD H (ErrorSign.ofDepth N).opposite D d Δ t)))


end MathlibNt.SieveTheory
