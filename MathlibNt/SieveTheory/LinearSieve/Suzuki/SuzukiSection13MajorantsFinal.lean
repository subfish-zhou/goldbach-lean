import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCutoffClaim146iiiSanitized

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

open BridgeAssembly CutoffCorrectedRatio

namespace Section13MajorantsFinal

/-- Exact conclusion of the already-closed moving Claim 14.6(iii). -/
def MovingClaim146iiiConclusion
    (H : Section13HatLayers) (d Δ : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    ∀ (sign : ErrorSign) (s : ℝ),
      2 + sign.epsilon ≤ s → s ≤ sourceSigma D d →
      (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) <
        (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
          lambda H sign D d 0 s

/-- Semantic audit: both sign-indexed bridges use literally the same `Qhat`.
There is no plus/minus choice of scalar solution at this interface. -/
theorem bridge_Qhat_sign_independent
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    (section13_bridgeAtThree hH ErrorSign.plus).Qhat =
      (section13_bridgeAtThree hH ErrorSign.minus).Qhat := rfl

/-- Consequently one honest Lemma-10.28 majorant supplies both sign-indexed
arguments expected by the moving Claim-14.6 theorem. -/
noncomputable def duplicateQhatMajorant
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (Q : CutoffMajorant (section13Qhat H)) :
    ∀ sign, CutoffMajorant (section13_bridgeAtThree hH sign).Qhat :=
  fun _ => Q

/-- Exact thin assembly into the closed moving Claim 14.6(iii).  This theorem is
included only to expose the semantic wiring; constructing `Q` from compact
initial data is the still-missing upstream Lemma-10.28 adapter. -/
theorem moving_claim14_6_iii_of_singleQhatMajorant
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {d Δ : ℝ} (hd : 0 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (Q : CutoffMajorant (section13Qhat H)) :
    MovingClaim146iiiConclusion H d Δ := by
  exact moving_claim14_6_iii_of_source_contract_and_cutoffMajorants
    hH hd hΔ0 hΔ1 (duplicateQhatMajorant hH Q)

/-- Historical compact-input audit boundary.  The endpoint-derivative blocker has
been removed by the corrected `Ioc` first-crossing interface.  This structure is
retained only as a record of the former mismatch and is not used downstream. -/
structure QhatCompactInitialData
    (H : Section13HatLayers) where
  S : ℝ
  four_le_S : 4 ≤ S
  endpoint_dde :
    HasDerivAt (section13Qhat H)
      (-(2 * section13Qhat H 3 + section13Qhat H (3 - 1)) / 3) 3
  values : Set.Icc (3 : ℝ) S → ℝ
  values_eq : ∀ u, values u = section13Qhat H u


end Section13MajorantsFinal
end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
