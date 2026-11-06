import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointFiniteAbsorption
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISharpRawEndpoint
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIPositiveDeltaDecay

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

/-- Exact expansion of `caseIIEndpointErr` used by the positive-`Δ` packet.
The algebraic and `q_D(3)` endpoint terms are not merged: their distinct
logarithmic scales remain visible. -/
theorem caseIIEndpointErr_eq_positiveDelta_packet_expansion
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D y z : ℕ} {w d Δ σ C K B0 s : ℝ}
    (hw : w = (D : ℝ) ^ (1 / σ)) :
    caseIIEndpointErr S H N D y z d Δ σ C K B0 s =
      B0 + suzukiVProduct S (z : ℝ) *
        (caseIIPositiveDeltaIntegralPart
            H N (D : ℝ) (y : ℝ) d Δ σ C K s +
          caseIINonIntegralEndpointCorrections
            H N (D : ℝ) (y : ℝ) w d Δ σ C K s) := by
  unfold caseIIEndpointErr caseIIPositiveDeltaIntegralPart
    caseIINonIntegralEndpointCorrections caseIIEndpointSigma11 caseIIEndpointQD
  rw [hw]
  ring



end MathlibNt.SieveTheory
