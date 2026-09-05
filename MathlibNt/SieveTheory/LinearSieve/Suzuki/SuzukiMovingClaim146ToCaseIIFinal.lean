import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaClaim146iII
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedConcreteRelativeAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceRoundedGeometryPacket
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceCaseIIFinalEventual
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseSplitFinal

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- Exact conclusion exported by the moving Claim 14.6(iii) assembly.  Keeping
this conclusion as a named interface lets this consumer compile even when the
large upstream cutoff-majorant module has not yet been installed as an import. -/
def MovingClaim14_6iiiAtSource
    (H : Section13HatLayers) (d Δ : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    ∀ (sign : ErrorSign) (s : ℝ),
      2 + sign.epsilon ≤ s → s ≤ sourceSigma D d →
      (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) <
        (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
          lambda H sign D d 0 s

/-- The genuine discrete Case-II assembly boundary.  Its conclusion is the
relative-bracket estimate, not the downstream Claim-14.5 bound.  Both cutoffs
are the literal natural ceilings used by the production endpoint. -/
def MovingCaseIIRelativeAssembler
    (Tdisc : ℕ → ℝ → ℝ → ℝ) (S : BoundingSieve)
    (H : Section13HatLayers) (B₀ : ℕ → ℕ → ℝ)
    (d Δ C K : ℝ) : Prop :=
  ∀ (N D : ℕ) (s : ℝ), Odd N → 1 < s → s ≤ 3 →
    let y : ℕ := ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊
    let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
    SourceRoundedGeometryPacket S D y z d s →
    Claim14_6_MonotoneLambdaPremise H (D : ℝ) d (sourceSigma (D : ℝ) d) →
    Claim14_6_MonotoneQPremise H (D : ℝ) d Δ (sourceSigma (D : ℝ) d) →
    ((∫ t in (3 : ℝ)..sourceSigma (D : ℝ) d,
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤
      (1 - 1 / sourceSigma (D : ℝ) d) ^ (1 - Δ) *
        lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 3) →
    Tdisc N (D : ℝ) (z : ℝ) ≤
      B₀ N D + suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 N s +
          ((C * Real.exp (Real.sqrt K)) * errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ)) *
          caseIIConcreteRoundedRelativeBracket
            N (D : ℝ) d Δ (sourceSigma (D : ℝ) d) C K)

/-- The remaining normalization from the source recurrence to the published
Claim-14.5 scale.  This is a coefficient comparison, rather than Claim 14.5
itself, and therefore does not assume the downstream conclusion. -/
def MovingCaseIINormalization
    (S : BoundingSieve) (H : Section13HatLayers)
    (B₀ : ℕ → ℕ → ℝ) (d Δ σ K C C145 : ℝ) : Prop :=
  ∀ (N D : ℕ) (s : ℝ), Odd N → 1 < s → s ≤ 3 →
    let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
    B₀ N D + suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 N s +
          (C * Real.exp (Real.sqrt K)) * errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ)) ≤
      C145 * claim14_5Scale S H N (D : ℝ) d Δ σ K s

/-- Natural-parameter version of the publication conclusion.  Unlike the
real-parameter convenience wrapper in `SuzukiClaim145CaseSplitFinal`, this form
retains the literal natural parameter consumed by the rounded endpoint. -/
def Claim14_5NatEventualAt
    (Tdisc : ℕ → ℝ → ℝ → ℝ) (S : BoundingSieve)
    (H : Section13HatLayers) (N : ℕ) (d Δ σ K s C145 : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℕ, D₀ ≤ (D : ℝ) →
    Claim14_5Bound Tdisc S H N (D : ℝ)
      (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) d Δ σ K s C145

/-- Moving Claims 14.6(i)--(iii), the source relative bracket, and exact
natural-ceiling geometry close the Case-II branch.  All thresholds are merged
before the natural parameter `D` is introduced. -/
theorem claim14_5_caseII_natEventual_of_movingClaim146
    {Tdisc : ℕ → ℝ → ℝ → ℝ} {S : BoundingSieve}
    {H : Section13HatLayers} {B₀ : ℕ → ℕ → ℝ}
    {N : ℕ} {d Δ σ K C C145 s : ℝ}
    (hH : Section13HatContract H 2) (hN : Odd N)
    (hd1 : 1 < d) (hd : 7 / (1 - Δ) < d)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hs1 : 1 < s) (hs3 : s ≤ 3)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hF0 : 0 ≤ finiteSourceLayer 1 2 N 3)
    (hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2)
    (hscaleNonneg : ∀ D : ℕ,
      0 ≤ (C * Real.exp (Real.sqrt K)) * errorEnvelope H N (D : ℝ) d s *
        (Real.log (D : ℝ)) ^ (-Δ))
    (hcert : MovingClaim14_6TailCertificate H 2 d Δ)
    (hmovingIII : MovingClaim14_6iiiAtSource H d Δ)
    (hassemble : MovingCaseIIRelativeAssembler Tdisc S H B₀ d Δ C K)
    (hnormalize : MovingCaseIINormalization S H B₀ d Δ σ K C C145) :
    Claim14_5NatEventualAt Tdisc S H N d Δ σ K s C145 := by
  obtain ⟨Dg, hDg, hgeom⟩ :=
    exists_sourceSigma_doubleRounded_geometry_threshold d hd1
  obtain ⟨D12, hD12, h12⟩ :=
    eventually_claim14_6_i_ii_at_sourceSigma_of_tailCertificate
      hH hd1 (by linarith) rfl hcert
  obtain ⟨D3, hD3, h3⟩ := hmovingIII
  obtain ⟨Db, hDb, hbracket⟩ :=
    exists_caseIIConcreteRoundedRelativeBracket_lt_one_threshold
      N K C d Δ hF0 hF1 hK hC hΔ0 hΔ1 hd
  let D₀ : ℝ := max Dg (max D12 (max D3 Db))
  refine ⟨D₀, hDg.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hDgD : Dg ≤ (D : ℝ) := (le_max_left Dg _).trans hD
  have hD12D : D12 ≤ (D : ℝ) :=
    (le_max_left D12 _).trans ((le_max_right Dg _).trans hD)
  have hD3D : D3 ≤ (D : ℝ) :=
    (le_max_left D3 Db).trans ((le_max_right D12 _).trans
      ((le_max_right Dg _).trans hD))
  have hDbD : Db ≤ (D : ℝ) :=
    (le_max_right D3 Db).trans ((le_max_right D12 _).trans
      ((le_max_right Dg _).trans hD))
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hg := hgeom S D hDgD s hs1 hs3
  have h12D := h12 (D : ℝ) hD12D
  have hsign3 : 2 + (ErrorSign.ofDepth N).epsilon ≤ (3 : ℝ) := by
    rw [ErrorSign.ofDepth_of_odd hN]
    norm_num [ErrorSign.epsilon]
  have hiii := (h3 (D : ℝ) hD3D (ErrorSign.ofDepth N) 3
    hsign3 hg.h3σ).le
  have hass := hassemble N D s hN hs1 hs3 hg h12D.1 h12D.2 hiii
  have hscale := hscaleNonneg D
  have hclosed := source_caseII_close_relative_bracket
    (suzukiVProduct_pos S (z : ℝ)).le hscale (hbracket (D : ℝ) hDbD) hass
  have hnorm := hnormalize N D s hN hs1 hs3
  unfold Claim14_5Bound
  exact hclosed.trans hnorm

/-- Exact Case-I/Case-II split with a natural rounded cutoff.  The branch is the
same tagged split exported by `SuzukiClaim145CaseSplitFinal`; Case II is supplied
by the moving Claim-14.6 closure above, while Case I remains its independent
producer. -/
theorem claim14_5_natEventual_exact_case_split_with_movingClaim146_caseII
    {Tdisc : ℕ → ℝ → ℝ → ℝ} {S : BoundingSieve}
    {H : Section13HatLayers} {B₀ : ℕ → ℕ → ℝ}
    {N : ℕ} {d Δ σ K C C145 D C1 ΘK s : ℝ}
    (hdom : s ∈ SuzukiFiniteContinuousLayers.suzukiParityDomainOne 2 N)
    (hsσ : s ≤ σ) (hlarge : C1 * K ^ ΘK < Real.log D)
    (hH : Section13HatContract H 2)
    (hd1 : 1 < d) (hd : 7 / (1 - Δ) < d)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hF0 : 0 ≤ finiteSourceLayer 1 2 N 3)
    (hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2)
    (hscaleNonneg : ∀ D : ℕ,
      0 ≤ (C * Real.exp (Real.sqrt K)) * errorEnvelope H N (D : ℝ) d s *
        (Real.log (D : ℝ)) ^ (-Δ))
    (hcert : MovingClaim14_6TailCertificate H 2 d Δ)
    (hmovingIII : MovingClaim14_6iiiAtSource H d Δ)
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
    exact claim14_5_caseII_natEventual_of_movingClaim146 hH hN hd1 hd hΔ0 hΔ1
      hs1 hs3 hC hK hF0 hF1 hscaleNonneg hcert hmovingIII hassemble hnormalize)


end MathlibNt.SieveTheory
