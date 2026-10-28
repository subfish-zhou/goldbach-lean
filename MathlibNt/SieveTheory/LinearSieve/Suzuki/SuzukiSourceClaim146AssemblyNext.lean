import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13BridgeAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingDDEAsymptoticClosure
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1028FirstCrossing

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SourceClaim146AssemblyNext

open BridgeAssembly


/-- The elementary moving-cutoff comparison still needed between Lemma 10.28's
`log(es)` gain and the perturbation logarithm.  This is numerical: it mentions
no hat function, DDE certificate, integral, or Claim 14.6 conclusion. -/
def SourceCutoffLogDomination
    (K A d M : ℝ) : Prop :=
  0 < d ∧
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    M ≤ sourceSigma D d ∧ ∀ t : ℝ, M ≤ t → t ≤ sourceSigma D d →
      2 * (d + 1) * K ^ 2 * A *
          max 1 (Real.log (1 + t ^ d / Real.log D)) ≤
        Real.log (Real.exp 1 * t)

/-- Source-range-corrected form of the moving ratio.  The older
`Proposition131MovingDelayedCurrentRatio` accidentally quantifies over every
`t ≥ M` at each fixed `D`, rather than `M ≤ t ≤ sourceSigma D d`. -/
def Proposition131MovingDelayedCurrentRatioOnSource
    (H : Section13HatLayers) (sign : ErrorSign) (d M : ℝ) : Prop :=
  0 < d ∧ 1 < M ∧
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    M ≤ sourceSigma D d ∧
    ∀ t : ℝ, M ≤ t → t ≤ sourceSigma D d →
      2 * (d + 1) * max 1 (Real.log (1 + t ^ d / Real.log D)) *
          weightedHat H sign t ≤ t * H.T sign.opposite (t - 1)


end SourceClaim146AssemblyNext
end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
