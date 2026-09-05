import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIFinalBoundary
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBaseOneSameC
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIOddSuccessorSameC
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144FiniteInductionFinal

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

theorem lemma14_4_caseII_total_sameC_eventually_at_sourceSigma
    {S : BoundingSieve} {H : Section13HatLayers}
    {B₀ : ℕ → ℕ → ℝ} {N : ℕ} {d Δ C K s : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hC : 0 < C) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hs1 : 1 < s) (hs3 : s ≤ 3)
    (hrelative : Lemma144CaseIIOddRoundedRelativeProducer S H B₀ d Δ C K)
    (hnormalize : Lemma144CaseIIOddEndpointGapNormalization S H B₀ d Δ C K)
    (hD : ∀ᶠ D : ℕ in atTop, 1 < (D : ℝ))
    (hdom : s ∈ suzukiParityDomainOne 2 N)
    (hroot2 : ∀ᶠ D : ℕ in atTop, 2 ≤ (D : ℝ) ^ (1 / s))
    (hN : Odd N) :
    Lemma144CaseIISameCEventuallyAtSourceSigma S H N d Δ C K s := by
  have hbase : Lemma144CaseIIBaseOneSameCProducer S H d Δ C K s :=
    lemma14_4_caseII_base_one_sameC_producer
      hH.toSection13HatContract (by linarith) hΔ0 hΔ1 hC hK hlocal hs1 hs3
  have hodd : Lemma144CaseIIOddSuccessorSameCProducer S H d Δ C K s :=
    lemma14_4_caseII_odd_successor_sameC_producer_of_endpoint_gap
      hrelative hnormalize hs1 hs3
  exact lemma14_4_caseII_sameC_eventually_at_sourceSigma_of_base_successor
    hD hdom hs3 hroot2 (le_trans (by norm_num) hK) hlocal hbase hodd hN

def Lemma144UniformNatCeilRestrictedAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ) (Q : ℝ → Prop) : Prop :=
  ∀ D : ℕ, Dmin ≤ D → 2 ≤ D →
    ∀ x : ℝ, x ∈ KappaOneModel.parityDomain 2 N → Q x →
    2 ≤ ⌈(D : ℝ) ^ (1 / x)⌉₊ →
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / x)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / x)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N x +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H N (D : ℝ) d x *
              (Real.log (D : ℝ)) ^ (-Δ))

theorem lemma144UniformNatCeilAt_of_restricted_cases
    {S : BoundingSieve} {H : Section13HatLayers}
    {C K d Δ : ℝ} {N DI DII : ℕ} {QI QII : ℝ → Prop}
    (hcover : ∀ x, x ∈ KappaOneModel.parityDomain 2 N → QI x ∨ QII x)
    (hI : Lemma144UniformNatCeilRestrictedAt S H C K d Δ N DI QI)
    (hII : Lemma144UniformNatCeilRestrictedAt S H C K d Δ N DII QII) :
    Lemma144UniformNatCeilAt S H C K d Δ N (max DI DII) := by
  intro D hD hD2 x hx hz
  rcases hcover x hx with hxI | hxII
  · exact hI D ((le_max_left DI DII).trans hD) hD2 x hx hxI hz
  · exact hII D ((le_max_right DI DII).trans hD) hD2 x hx hxII hz

theorem lemma14_4_full_finiteDepth_final
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (depth : ℕ)
    (QI QII : ℕ → ℝ → Prop)
    (hcover : ∀ M x, x ∈ KappaOneModel.parityDomain 2 M →
      QI M x ∨ QII M x)
    (hbase : ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      Lemma144UniformNatCeilAt S H C K d Δ 1 Dmin)
    (hcaseI : ∀ N Dmin : ℕ,
      1 ≤ N → N < depth → 2 ≤ Dmin →
      Lemma144GlobalDepthAt S H C K d Δ N Dmin →
      ∃ DI : ℕ, Dmin ≤ DI ∧
        Lemma144UniformNatCeilRestrictedAt
          S H C K d Δ (N + 1) DI (QI (N + 1)))
    (hcaseII : ∀ N Dmin : ℕ,
      1 ≤ N → N < depth → 2 ≤ Dmin →
      Lemma144GlobalDepthAt S H C K d Δ N Dmin →
      ∃ DII : ℕ, Dmin ≤ DII ∧
        Lemma144UniformNatCeilRestrictedAt
          S H C K d Δ (N + 1) DII (QII (N + 1))) :
    ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ depth →
        Lemma144GlobalDepthAt S H C K d Δ N Dmin := by
  apply lemma14_4_finiteDepth_induction_final S H C K d Δ depth hbase
  intro N Dmin hN hNdepth hDmin hIH
  obtain ⟨DI, hIDI, hI⟩ := hcaseI N Dmin hN hNdepth hDmin hIH
  obtain ⟨DII, hIDII, hII⟩ := hcaseII N Dmin hN hNdepth hDmin hIH
  refine ⟨max DI DII, hIDI.trans (le_max_left _ _), ?_⟩
  exact lemma144UniformNatCeilAt_of_restricted_cases
    (hcover (N + 1)) hI hII


end MathlibNt.SieveTheory
