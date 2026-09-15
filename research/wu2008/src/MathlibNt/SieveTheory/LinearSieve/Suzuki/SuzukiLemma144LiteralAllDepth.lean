import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145Complete
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145OddLowStripSmallLogActual
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISourceLargeLogPointwiseProducer
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIEvenEndpointSourceLargeLogPointwise
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIISourceLargeLogMoving
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144NoDminAllDepthGlue

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 3000000

/-- Literal all-depth, cutoff-two Suzuki bound under the printed source
parameters, with the omitted source-small odd strip supplied by the separately
named low-strip extension.  All constants precede `K`, depth, `D`, and `s`. -/
theorem exists_lemma14_4_literal_allDepth_with_lowStrip_extension
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 0 < C1min ∧
      ∀ C1 : ℝ, C1min ≤ C1 →
        ∃ C145 Clow C : ℝ,
          0 < C145 ∧ 0 ≤ Clow ∧ 3 ≤ C ∧
          ∀ K : ℝ, 2 ≤ K → HasDimensionOneLocalProductBound S K →
            ∀ N : ℕ, 1 ≤ N →
              Lemma144MovingDomainNatCeilAt S H C K d Δ N 2 := by
  obtain ⟨C1claim, _CBclaim, hC1claim, _hCBclaim, hclaimAll⟩ :=
    exists_claim145_source_complete S H hsrc.toGeneric hsrc.hDelta_pos
      hsrc.hDelta_lt hsrc.h14_1 hH
  obtain ⟨C1strict, CBstrict, hC1strict, hCBstrict, hstrictAll⟩ :=
    exists_lemma14_4_caseI_final_producer_sourceLargeLog_pointwise S H hH hsrc
  obtain ⟨C1even, CBeven, hC1even, hCBeven, hevenAll⟩ :=
    exists_lemma14_4_caseI_evenEndpoint_sourceLargeLog_pointwise S H hH hsrc
  obtain ⟨C1caseII, hC1caseII, hcaseIIAll⟩ :=
    exists_lemma144_caseII_odd_sameC_sourceLargeLog_uniform_moving
      S H hH hsrc (show 2 ≤ (2 : ℕ) by omega)
  let C1min : ℝ := max 1 (max C1claim (max C1strict (max C1even C1caseII)))
  have hC1min : 0 < C1min := by
    exact zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  have hparts :
      C1claim ≤ C1 ∧ C1strict ≤ C1 ∧ C1even ≤ C1 ∧ C1caseII ≤ C1 := by
    have hm : max C1claim (max C1strict (max C1even C1caseII)) ≤ C1 :=
      (le_max_right 1 _).trans (show C1min ≤ C1 from hC1)
    simpa only [max_le_iff] using hm
  obtain ⟨C145, hC145, hclaim⟩ := hclaimAll C1 hparts.1
  have hC10 : 0 ≤ C1 := hC1min.le.trans hC1
  obtain ⟨Clow, hClow, hlow⟩ :=
    claim145_odd_lowStrip_smallLog_actual S H hH hC10 hsrc.hTheta_pos
      hsrc.d_pos hsrc.h14_3 hsrc.hDelta_pos.le hsrc.hDelta_lt.le
  let C : ℝ := max 3 (max CBstrict (max CBeven
    (max (lemma144BaseOneGlobalConstant Δ)
      (max (claim145UniformNormalizationConstant C145 d)
        (claim145UniformNormalizationConstant Clow d)))))
  have hCparts := (show
      max 3 (max CBstrict (max CBeven
        (max (lemma144BaseOneGlobalConstant Δ)
          (max (claim145UniformNormalizationConstant C145 d)
            (claim145UniformNormalizationConstant Clow d))))) ≤ C from le_rfl)
  simp only [max_le_iff] at hCparts
  rcases hCparts with ⟨hC3, hCBstrict, hCBeven, hCbase, hCnorm, hClowNorm⟩
  have hCstrict : max 3 CBstrict ≤ C := max_le hC3 hCBstrict
  have hCeven : max 3 CBeven ≤ C := max_le hC3 hCBeven
  refine ⟨C145, Clow, C, hC145, hClow, hC3, ?_⟩
  intro K hK hlocal
  apply lemma14_4_noDmin_allDepth_of_sourceLarge_strict_even S H
    hC145.le hsrc.d_pos hCnorm hH hsrc.hDelta_lt hCbase hK hlocal
  · intro N D s hN hD hs hregime
    exact hclaim K N D s hK hlocal hD hs hregime
  · intro M D s hM hsdom hspred hs hsLower hlarge hsSigma hthreshold hglobal
    exact hstrictAll C1 C K M D s hparts.2.1 hCstrict hK hlocal hM hsdom
      hspred hs hsLower hlarge hsSigma hthreshold hglobal
  · intro M D hMeven hM hsSigma hlarge hglobal
    exact hevenAll C1 C K M D hparts.2.2.1 hCeven hK hlocal hMeven hM
      hlarge hglobal
  · intro N D s hN hD hsdom hsSigma hz hside hglobal
    have hodd : Odd (N + 1) := hside.1
    have hM3 : 3 ≤ N + 1 := by
      have hmod : (N + 1) % 2 = 1 := Nat.odd_iff.mp hodd
      omega
    have hs1 : 1 < s := by
      have hs1' : (2 : ℝ) - 1 < s := by
        simpa [KappaOneModel.parityDomain, Nat.odd_iff.mp hodd] using hsdom
      norm_num at hs1' ⊢
      exact hs1'
    by_cases hlarge : C1 * K ^ Θ < Real.log (D : ℝ)
    · apply caseII_sameCAt_to_literal_moving S H
      exact hcaseIIAll C1 C K (N + 1) D s hparts.2.2.2 hC3 hK hD hlocal
        hlarge hodd hM3 hs1 hside.2 (by simpa using hglobal)
    · have hsmall : Real.log (D : ℝ) ≤ C1 * K ^ Θ := le_of_not_gt hlarge
      by_cases hs2 : 2 ≤ s
      · exact actualClaim145_to_moving_at_common_constant S H hC145.le
          hsrc.d_pos hCnorm hH hD hsdom
          (hclaim K (N + 1) D s hK hlocal hD hs2 (Or.inl hsmall))
      · exact actualClaim145_to_moving_at_common_constant S H hClow
          hsrc.d_pos hClowNorm hH hD hsdom
          (hlow K (N + 1) D s hK hodd hlocal hD hs1
            (le_of_not_ge hs2) hsmall)


end MathlibNt.SieveTheory
