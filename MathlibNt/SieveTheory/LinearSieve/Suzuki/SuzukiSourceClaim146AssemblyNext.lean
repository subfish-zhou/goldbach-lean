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

/-- Cutoff-aware Lemma 10.29, derived directly from the honest Lemma-10.28
majorant.  No adjacent-value estimate is assumed. -/
theorem unitShift_of_cutoffMajorant
    {R : ℝ → ℝ} {β s : ℝ} (hDDE : Section10DDEApparatus R β)
    (Q : Lemma1028CutoffMajorant R) (hβ : β ≤ 3)
    (hs : Q.cutoff ≤ s) :
    s * Real.log (Real.exp 1 * s) * R s ≤ Q.A * R (s - 1) := by
  have hs4 : 4 ≤ s := Q.four_le_cutoff.trans hs
  have hs0 : 0 < s := by linarith
  have hR : 0 < R s := hDDE.positive s (by linarith)
  have hmaj := Q.majorizes_log s hs
  have henv := Q.envelope_slope_nonpos s hs
  have hscaled :
      s * ((1 / Q.A) * Real.log (Real.exp 1 * s)) * R s ≤ R (s - 1) := by
    have hm := mul_le_mul_of_nonneg_left hmaj hs0.le
    have hm' := mul_le_mul_of_nonneg_right hm hR.le
    nlinarith
  have hA : 0 < Q.A := zero_lt_one.trans_le Q.one_le_A
  calc
    s * Real.log (Real.exp 1 * s) * R s =
        Q.A * (s * ((1 / Q.A) * Real.log (Real.exp 1 * s)) * R s) := by
          field_simp [ne_of_gt hA]
    _ ≤ Q.A * R (s - 1) := mul_le_mul_of_nonneg_left hscaled hA.le

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

/-- Exact adapter to the existing certificate theorem.  The extra premise is
displayed deliberately: it is precisely the erroneous global-in-`t` extension
which cannot follow from a moving-source cutoff estimate. -/
theorem movingCertificate_of_globalRatioExtension
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (sign : ErrorSign) {d : ℝ}
    (Q : Lemma1028CutoffMajorant (section13_bridgeAtThree hH sign).Qhat)
    (hglobal : Proposition131MovingDelayedCurrentRatio H sign d Q.cutoff) :
    MovingDDEAsymptoticCertificate H sign d Q.cutoff :=
  movingDDEAsymptoticCertificate_of_proposition131_ratio
    hH.toSection13HatContract sign hglobal

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
