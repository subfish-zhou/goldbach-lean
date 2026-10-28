import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingDerivativeDDELargeRange
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingDerivativeDDECompactRange
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingClaim146iIICorrected
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedEndpointTransport
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceContractionGap
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceRoundedGeometryPacket

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne
open SwitchingPrinciple.SuzukiLemma144KappaOne.Section13QhatMajorantClosure
open SwitchingPrinciple.SuzukiLemma144KappaOne.BridgeAssembly
open SwitchingPrinciple.SuzukiLemma144KappaOne.CutoffCorrectedRatio

set_option maxHeartbeats 1600000

namespace SwitchingPrinciple.SuzukiLemma144KappaOne

/-- The large source range supplied by Proposition 13.1 and the fixed compact
head supplied by continuity/positivity merge into the corrected pointwise
certificate.  In particular, the certificate is produced here and is not an
assumption of either Claim 14.6 or Case II. -/
theorem derivativeDDECertificateOnSource_of_singleQhatMajorant
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {d : ℝ} (hd : 0 < d)
    (Q : CutoffMajorant (section13Qhat H)) :
    MovingDerivativeDDECertificateOnSource H d := by
  obtain ⟨M, Dl, hM1, hM4, hDl, hlarge⟩ :=
    moving_derivativeDDE_largeRange_of_section13HatSourceContract hH hd Q
  obtain ⟨Dc, hDc, hcompact⟩ :=
    eventually_derivativeDDE_domination_on_compactRange
      (M := M) hH.toSection13HatContract hd.le (by linarith [hM4])
  let D₀ : ℝ := max Dl Dc
  refine ⟨D₀, hDl.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hDlD : Dl ≤ D := (le_max_left Dl Dc).trans hD
  have hDcD : Dc ≤ D := (le_max_right Dl Dc).trans hD
  rcases hlarge D hDlD with ⟨hMσ, hlargeD⟩
  refine ⟨hM4.trans hMσ, ?_⟩
  intro sign ε t hε ht htσ
  by_cases htM : t ≤ M
  · exact hcompact D hDcD sign ε t hε ht htM
  · exact hlargeD sign ε t hε (le_of_not_ge htM) htσ.le

/-- All three moving clauses at the literal source endpoint.  The same internally
constructed scalar majorant feeds both the corrected (i),(ii) certificate and
the already closed (iii) assembly. -/
theorem eventually_claim14_6_full_internal_at_sourceSigma
    {H : Section13HatLayers} {d Δ : ℝ}
    (hH : Section13HatSourceContract H) (hd1 : 1 < d)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      Claim14_6_MonotoneLambdaPremise H D d (sourceSigma D d) ∧
      Claim14_6_MonotoneQPremise H D d Δ (sourceSigma D d) ∧
      (∀ (sign : ErrorSign) (s : ℝ),
        2 + sign.epsilon ≤ s → s ≤ sourceSigma D d →
        (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) <
          (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
            lambda H sign D d 0 s) := by
  let Q : CutoffMajorant (section13Qhat H) :=
    section13Qhat_cutoffMajorant_internal hH
  have hcert : MovingDerivativeDDECertificateOnSource H d :=
    derivativeDDECertificateOnSource_of_singleQhatMajorant hH (by linarith) Q
  obtain ⟨D12, hD12, h12⟩ :=
    eventually_claim14_6_i_ii_at_sourceSigma_of_derivativeDDE
      hH.toSection13HatContract hd1 (by linarith) hcert
  obtain ⟨D3, hD3, h3⟩ :=
    moving_claim14_6_iii_of_section13HatSourceContract
      (d := d) (Δ := Δ) hH (by linarith) hΔ0 hΔ1
  let D₀ : ℝ := max D12 D3
  refine ⟨D₀, hD12.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hD12D : D12 ≤ D := (le_max_left D12 D3).trans hD
  have hD3D : D3 ≤ D := (le_max_right D12 D3).trans hD
  exact ⟨(h12 D hD12D).1, (h12 D hD12D).2, h3 D hD3D⟩

end SwitchingPrinciple.SuzukiLemma144KappaOne


end MathlibNt.SieveTheory
