import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIIntegralTransportRelative
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiNatCeilPowerCarrier

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000


/-- Euler products are literally unchanged by replacing a strict real cutoff
with its natural ceiling. -/
theorem suzukiVProduct_natCeil_real_eq
    (S : BoundingSieve) {x : ℝ} {z : ℕ} (hz : z = ⌈x⌉₊) :
    suzukiVProduct S (z : ℝ) = suzukiVProduct S x := by
  exact suzukiVProduct_natCeil_eq S hz


/-- The rounded integral term is bounded at the genuine real cubic coordinate.
No equality between the cube root and the cast of its ceiling is needed. -/
theorem caseIIRoundedIntegralPart_source_relative
    (H : Section13HatLayers) {N : ℕ} {D yr d Δ σ C K s : ℝ}
    (hyr : yr = D ^ (1 / (3 : ℝ)))
    (hD : 1 < D) (hs : 0 < s) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hcut : 0 ≤ (1 - 1 / σ) ^ (1 - Δ))
    (hiii : (∫ t in (3 : ℝ)..σ,
        qD H (ErrorSign.ofDepth N).opposite D d Δ t) ≤
      (1 - 1 / σ) ^ (1 - Δ) *
        lambda H (ErrorSign.ofDepth N) D d 0 3)
    (hcubic : lambda H (ErrorSign.ofDepth N) D d 0 3 ≤
      perturbation D d 0 3 *
        lambda H (ErrorSign.ofDepth N) D d 0 s) :
    caseIIPositiveDeltaIntegralPart H N D yr d Δ σ C K s ≤
      C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
        (Real.log D) ^ (-Δ) *
        ((1 + 3 * K / Real.log D) *
          (1 - 1 / σ) ^ (1 - Δ) * perturbation D d 0 3) := by
  rw [hyr]
  exact caseIIPositiveDeltaIntegralPart_source_exact_relative
    H hD hs hC hK hcut hiii hcubic


end MathlibNt.SieveTheory
