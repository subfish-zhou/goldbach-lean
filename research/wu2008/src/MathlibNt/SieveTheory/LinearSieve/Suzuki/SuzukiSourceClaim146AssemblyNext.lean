import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13BridgeAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingDDEAsymptoticClosure
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaClaim146SourceAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1028FirstCrossing

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SourceClaim146AssemblyNext

open BridgeAssembly

/-- The genuine upstream Lemma-10.28 output, with its honest eventual cutoff.
It contains neither a delayed/current ratio nor any Claim-14.6 conclusion. -/
abbrev Lemma1028CutoffMajorant (R : ℝ → ℝ) :=
  Section10Lemma1028FirstCrossing.Section10CommonMajorant R

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

private lemma log_e_mul_pos {s : ℝ} (hs : 3 ≤ s) :
    0 < Real.log (Real.exp 1 * s) := by
  have hs1 : 1 ≤ s := by linarith
  have hsne : s ≠ 0 := by linarith
  rw [Real.log_mul (Real.exp_ne_zero 1) hsne, Real.log_exp]
  linarith [Real.log_nonneg hs1]


/-- The exact additional bridge/numerical fact required to turn the cutoff
majorant into the source-range ratio.  It is kept visible rather than hidden in
a fake "majorant": the current `Section13HatSection10BridgeAtThree` is
sign-indexed and does not expose that its two instances share the same `Qhat`
and comparison constant. -/
structure CrossSignCutoffTransport
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (d : ℝ) where
  sign : ErrorSign
  ratioOnSource : ∃ M : ℝ,
    Proposition131MovingDelayedCurrentRatioOnSource H sign d M


/-- Exact status ledger.  The honest cutoff majorant closes the cutoff-aware
unit shift.  The current APIs still require (i) repair of the moving-ratio
quantifier, (ii) filling the bounded interval below the Lemma-10.28 cutoff in
Proposition 13.1(iii), and (iii) the independent Lemma-13.3 compact head.
Consequently Claim 14.6(iii) cannot honestly be exported from `hH + Q` alone. -/
structure RemainingClaim146iiiSourceInputs
    (H : Section13HatLayers) (d Δ gap M : ℝ) : Prop where
  ratioOnSource : ∀ sign,
    Proposition131MovingDelayedCurrentRatioOnSource H sign d M
  tailDecay : Proposition131TailDecayContract H
  perturbation : FixedCompactPerturbationContract d M
  weightedHead : Lemma133WeightedHeadContract H d Δ gap M


end SourceClaim146AssemblyNext
end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
