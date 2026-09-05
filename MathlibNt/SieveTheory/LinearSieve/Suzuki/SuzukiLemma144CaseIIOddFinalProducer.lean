import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIEndpointGap
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBracketGapQuantitative
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ErrorEnvelopeTransportFull
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ExplicitRemaindersSourceOrder
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceCaseIIFinalEventual
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedConcreteRelativeAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIOddFinalClosure

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 2400000

/-- The exact source-endpoint Claim 14.6 packet needed by the rounded producer.
It is strictly upstream of the desired Lemma 14.4 successor conclusion. -/
def Lemma144CaseIIOddSourceClaim146
    (H : Section13HatLayers) (d Δ : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    Claim14_6_MonotoneLambdaPremise H D d (sourceSigma D d) ∧
    Claim14_6_MonotoneQPremise H D d Δ (sourceSigma D d) ∧
    ∀ (sign : ErrorSign) (s : ℝ),
      2 + sign.epsilon ≤ s → s ≤ sourceSigma D d →
      (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) <
        (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
          lambda H sign D d 0 s

/-- Exact accepted raw producer boundary.  This is the conclusion of
`caseII_total_le_doubleRounded_direct_concrete_relative_natCeil` after its
source geometry and Claim-14.6 premises have been supplied.  It contains the
recursive raw base `B₀`, but does not contain or assume the desired successor. -/
def Lemma144CaseIIOddRawRoundedProducer
    (S : BoundingSieve) (H : Section13HatLayers)
    (B₀ : ℕ → ℕ → ℝ) (d Δ C K : ℝ) : Prop :=
  ∀ (N D : ℕ) (s : ℝ), Odd N → 3 ≤ N → 1 < s → s ≤ 3 →
    SourceRoundedGeometryPacket S D
      ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊ ⌈(D : ℝ) ^ (1 / s)⌉₊ d s →
    Claim14_6_MonotoneLambdaPremise H (D : ℝ) d (sourceSigma (D : ℝ) d) →
    Claim14_6_MonotoneQPremise H (D : ℝ) d Δ (sourceSigma (D : ℝ) d) →
    ((∫ t in (3 : ℝ)..sourceSigma (D : ℝ) d,
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤
      (1 - 1 / sourceSigma (D : ℝ) d) ^ (1 - Δ) *
        lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 3) →
    let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = N % 2),
        suzukiSourceV S n D z) ≤
      B₀ N D + suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 N s +
          (C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ)) *
          caseIIConcreteRoundedRelativeBracket N (D : ℝ) d Δ
            (sourceSigma (D : ℝ) d) C K)

/-- Source geometry, the source Claim-14.6 packet, the eventual concrete
bracket, and the raw double-rounded producer construct the rounded-relative
producer required by the same-`C` terminal algebra. -/
theorem lemma144_caseII_odd_roundedRelativeProducer_of_raw
    (S : BoundingSieve) (H : Section13HatLayers)
    {B₀ : ℕ → ℕ → ℝ} {d Δ C K : ℝ}
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (h146 : Lemma144CaseIIOddSourceClaim146 H d Δ)
    (hraw : Lemma144CaseIIOddRawRoundedProducer S H B₀ d Δ C K) :
    Lemma144CaseIIOddRoundedRelativeProducer S H B₀ d Δ C K := by
  intro N hN hN3
  obtain ⟨Dg, hDg, hg⟩ := exists_sourceSigma_doubleRounded_geometry_threshold d hd1
  obtain ⟨D146, hD146, h146D⟩ := h146
  have hF0 : 0 ≤ finiteSourceLayer 1 2 N 3 := by
    apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) N
    simp [KappaOneModel.parityDomain, Nat.odd_iff.mp hN]
    norm_num
  have hNm : (N - 1) % 2 = 0 := by
    have hnmod : N % 2 = 1 := Nat.odd_iff.mp hN
    omega
  have hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2 := by
    apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
    simp [KappaOneModel.parityDomain, hNm]
  obtain ⟨Db, hDb, hb⟩ :=
    exists_caseIIConcreteRoundedRelativeBracket_lt_one_threshold
      N K C d Δ hF0 hF1 hK hC hΔ0 hΔ1 hd
  let D₀ : ℝ := max Dg (max D146 Db)
  refine ⟨D₀, hDg.trans_le (le_max_left _ _), ?_⟩
  intro D hD s hs1 hs3
  have hDgD : Dg ≤ (D : ℝ) := (le_max_left Dg _).trans hD
  have hD146D : D146 ≤ (D : ℝ) :=
    (le_max_left D146 Db).trans ((le_max_right Dg _).trans hD)
  have hDbD : Db ≤ (D : ℝ) :=
    (le_max_right D146 Db).trans ((le_max_right Dg _).trans hD)
  have hgeom := hg S D hDgD s hs1 hs3
  obtain ⟨hi, hii, hiiiAll⟩ := h146D (D : ℝ) hD146D
  have hsign3 : 2 + (ErrorSign.ofDepth N).epsilon ≤ (3 : ℝ) := by
    rw [ErrorSign.ofDepth_of_odd hN]
    norm_num [ErrorSign.epsilon]
  have hiii := (hiiiAll (ErrorSign.ofDepth N) 3 hsign3 hgeom.h3σ).le
  refine ⟨hgeom.h3σ, hb (D : ℝ) hDbD, ?_⟩
  exact hraw N D s hN hN3 hs1 hs3 hgeom hi hii hiii

/-- Full odd same-`C` producer.  Claim 14.5 and its scaling bridge are consumed
internally; the only remaining discrete premise is the exact raw producer. -/
theorem lemma144_caseII_odd_sameC_producer_of_raw_and_scaling
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C K C145 s : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d)
    (hC : 0 < C) (hK : 0 < K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (h146 : Lemma144CaseIIOddSourceClaim146 H d Δ)
    (hraw : Lemma144CaseIIOddRawRoundedProducer S H
      (caseIIOddClaim145Endpoint S d) d Δ C K)
    (hs1 : 1 < s) (hs3 : s ≤ 3) :
    Lemma144CaseIIOddSuccessorSameCProducer S H d Δ C K s := by
  have hrelative : Lemma144CaseIIOddRoundedRelativeProducer S H
      (caseIIOddClaim145Endpoint S d) d Δ C K :=
    lemma144_caseII_odd_roundedRelativeProducer_of_raw S H hd1 hΔ0 hΔ1 hd
      hC.le hK.le h146 hraw
  have hscale : Lemma144CaseIIOddClaim145ScalingBridge S H d Δ C K C145 :=
    lemma144_caseII_odd_claim145_scaling_bridge S H
      hH hd1 hΔ0 hΔ1 hd hC hK hC145
  have hnormalize : Lemma144CaseIIOddEndpointGapNormalization S H
      (caseIIOddClaim145Endpoint S d) d Δ C K :=
    lemma144_caseII_odd_endpoint_gap_of_claim145_scaling_bridge S H
      hΔ0 hΔ1 hd hK hC145 hlocal hH hscale
  exact lemma14_4_caseII_odd_successor_sameC_producer_of_endpoint_gap
    hrelative hnormalize hs1 hs3

theorem lemma144_caseII_odd_sameC_producer_of_raw_internal
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C K C145 s : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d)
    (hC : 0 < C) (hK : 0 < K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hraw : Lemma144CaseIIOddRawRoundedProducer S H
      (caseIIOddClaim145Endpoint S d) d Δ C K)
    (hs1 : 1 < s) (hs3 : s ≤ 3) :
    Lemma144CaseIIOddSuccessorSameCProducer S H d Δ C K s := by
  have h146 : Lemma144CaseIIOddSourceClaim146 H d Δ := by
    simpa [Lemma144CaseIIOddSourceClaim146] using
      (eventually_claim14_6_full_internal_at_sourceSigma hH hd1 hΔ0 hΔ1)
  exact lemma144_caseII_odd_sameC_producer_of_raw_and_scaling S H
    hH hd1 hΔ0 hΔ1 hd hC hK hC145 hlocal h146 hraw hs1 hs3


end MathlibNt.SieveTheory
