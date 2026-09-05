import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingDerivativeDDELargeRange
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingDerivativeDDECompactRange
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingClaim146iIICorrected
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13QhatMajorantInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingClaim146ToCaseIIFinal

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

/-- Natural Case-II closure with Claims 14.6(i)--(iii) generated before the
natural source parameter is introduced. -/
theorem claim14_5_caseII_natEventual_of_internalClaim146
    {Tdisc : ℕ → ℝ → ℝ → ℝ} {S : BoundingSieve}
    {H : Section13HatLayers} {B₀ : ℕ → ℕ → ℝ}
    {N : ℕ} {d Δ σ K C C145 s : ℝ}
    (hH : Section13HatSourceContract H) (hN : Odd N)
    (hd1 : 1 < d) (hd : 7 / (1 - Δ) < d)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hs1 : 1 < s) (hs3 : s ≤ 3)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hF0 : 0 ≤ finiteSourceLayer 1 2 N 3)
    (hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2)
    (hscaleNonneg : ∀ D : ℕ,
      0 ≤ (C * Real.exp (Real.sqrt K)) * errorEnvelope H N (D : ℝ) d s *
        (Real.log (D : ℝ)) ^ (-Δ))
    (hassemble : MovingCaseIIRelativeAssembler Tdisc S H B₀ d Δ C K)
    (hnormalize : MovingCaseIINormalization S H B₀ d Δ σ K C C145) :
    Claim14_5NatEventualAt Tdisc S H N d Δ σ K s C145 := by
  obtain ⟨Dg, hDg, hgeom⟩ :=
    exists_sourceSigma_doubleRounded_geometry_threshold d hd1
  obtain ⟨D146, hD146, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma hH hd1 hΔ0 hΔ1
  obtain ⟨Db, hDb, hbracket⟩ :=
    exists_caseIIConcreteRoundedRelativeBracket_lt_one_threshold
      N K C d Δ hF0 hF1 hK hC hΔ0 hΔ1 hd
  let D₀ : ℝ := max Dg (max D146 Db)
  refine ⟨D₀, hDg.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hDgD : Dg ≤ (D : ℝ) := (le_max_left Dg _).trans hD
  have hD146D : D146 ≤ (D : ℝ) :=
    (le_max_left D146 Db).trans ((le_max_right Dg _).trans hD)
  have hDbD : Db ≤ (D : ℝ) :=
    (le_max_right D146 Db).trans ((le_max_right Dg _).trans hD)
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hg := hgeom S D hDgD s hs1 hs3
  obtain ⟨hi, hii, hiiiAll⟩ := h146 (D : ℝ) hD146D
  have hsign3 : 2 + (ErrorSign.ofDepth N).epsilon ≤ (3 : ℝ) := by
    rw [ErrorSign.ofDepth_of_odd hN]
    norm_num [ErrorSign.epsilon]
  have hiii := (hiiiAll (ErrorSign.ofDepth N) 3 hsign3 hg.h3σ).le
  have hass := hassemble N D s hN hs1 hs3 hg hi hii hiii
  have hclosed := source_caseII_close_relative_bracket
    (suzukiVProduct_pos S (z : ℝ)).le (hscaleNonneg D)
      (hbracket (D : ℝ) hDbD) hass
  have hnorm := hnormalize N D s hN hs1 hs3
  unfold Claim14_5Bound
  exact hclosed.trans hnorm

/-- Exact Case-I/Case-II split with the full moving Claim 14.6 generated
internally from the Section-13 source contract. -/
theorem claim14_5_natEventual_exact_case_split_with_internalClaim146_caseII
    {Tdisc : ℕ → ℝ → ℝ → ℝ} {S : BoundingSieve}
    {H : Section13HatLayers} {B₀ : ℕ → ℕ → ℝ}
    {N : ℕ} {d Δ σ K C C145 D C1 ΘK s : ℝ}
    (hdom : s ∈ SuzukiFiniteContinuousLayers.suzukiParityDomainOne 2 N)
    (hsσ : s ≤ σ) (hlarge : C1 * K ^ ΘK < Real.log D)
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hd : 7 / (1 - Δ) < d)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hF0 : 0 ≤ finiteSourceLayer 1 2 N 3)
    (hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2)
    (hscaleNonneg : ∀ D : ℕ,
      0 ≤ (C * Real.exp (Real.sqrt K)) * errorEnvelope H N (D : ℝ) d s *
        (Real.log (D : ℝ)) ^ (-Δ))
    (hassemble : MovingCaseIIRelativeAssembler Tdisc S H B₀ d Δ C K)
    (hnormalize : MovingCaseIINormalization S H B₀ d Δ σ K C C145)
    (hI : 2 + (N % 2 : ℕ) ≤ s → s ≤ σ →
      Claim14_5NatEventualAt Tdisc S H N d Δ σ K s C145) :
    Claim14_5NatEventualAt Tdisc S H N d Δ σ K s C145 := by
  have hbranch : Claim14_5ExactBranch 2 N s σ :=
    claim14_5ExactBranch_iff.mpr
      (claim14_5_exact_case_split hdom hsσ hlarge)
  exact hbranch.elim hI (fun hN hlo hup => by
    have hs1 : 1 < s := by norm_num at hlo ⊢; exact hlo
    have hs3 : s ≤ 3 := by norm_num at hup ⊢; exact hup
    exact claim14_5_caseII_natEventual_of_internalClaim146
      hH hN hd1 hd hΔ0 hΔ1 hs1 hs3 hC hK hF0 hF1 hscaleNonneg
      hassemble hnormalize)


end MathlibNt.SieveTheory
