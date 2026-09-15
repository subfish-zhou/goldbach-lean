import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1055SourceExpansion
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingZeroSpecialized
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiiReverseRatio

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 2400000

open BridgeAssembly
open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10CanonicalXi
open Section10Lemma1028PlusAssembly
open Section10Equation1053NonCircular
open Section10Equation1055SourceExpansion

/-- The normalized plus slope for `Qhat` is bounded below on the fixed initial
interval used by the first-crossing argument. -/
lemma section13Qhat_normalizedPlusSlope_bddBelow
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ B : ℝ, ∀ u ∈ Icc (3 : ℝ) (Real.exp 2 + 1),
      -normalizedMinusBase (section13Qhat H) xi u ≤ B := by
  let f : ℝ → ℝ := fun u => -normalizedMinusBase (section13Qhat H) xi u
  have hf : ContinuousOn f (Icc (3 : ℝ) (Real.exp 2 + 1)) := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hum0 : 0 < u - 1 := by linarith [hu.1]
    have hQu : 0 < section13Qhat H u :=
      section13Qhat_pos hH.toSection13HatContract hu0
    have hQc : ContinuousAt (section13Qhat H) u :=
      (section13Qhat_continuousOn hH.toSection13HatContract).continuousAt
        (Ioi_mem_nhds hu0)
    have hQmc : ContinuousAt (fun v : ℝ => section13Qhat H (v - 1)) u :=
      ((section13Qhat_continuousOn hH.toSection13HatContract).continuousAt
        (Ioi_mem_nhds hum0)).comp_of_eq
          (continuousAt_id.sub continuousAt_const) (by simp)
    have hbase : ContinuousAt (normalizedMinusBase (section13Qhat H) xi) u := by
      exact (((hQmc.neg.div (continuousAt_id.mul hQc)
        (mul_ne_zero (ne_of_gt hu0) (ne_of_gt hQu))).add
          xi_continuous.continuousAt).sub
            (continuousAt_const.div continuousAt_id (ne_of_gt hu0)))
    exact hbase.neg.continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hf
  refine ⟨B, ?_⟩
  intro u hu
  exact hB ⟨u, hu, rfl⟩

/-- Lemma 10.28, increasing-envelope half, for the canonical Section-13
solution `Qhat`.  The proof uses the genuine first crossing and the internal
(10.53)/(10.55) integration-by-parts estimate; neither a derivative sign nor a
unit-shift ratio is assumed. -/
theorem section13Qhat_reverseEnvelopeEdge
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Section10Lemma1028ReverseEnvelopeEdge (section13Qhat H) := by
  let h : FirstCrossingDDEApparatus (section13Qhat H) 3 :=
    { adjoint := section13AdjointPlus
      beta_ge_one := by norm_num
      continuous := (section13Qhat_continuousOn hH.toSection13HatContract).mono (by
        intro s hs
        norm_num at hs ⊢
        linarith)
      positive := by
        intro s hs
        exact section13Qhat_pos hH.toSection13HatContract (by linarith)
      original_dde := by
        intro s hs
        exact section13Qhat_dde hH.toSection13HatContract hs
      adjoint_positive := by
        intro s hs
        dsimp [section13AdjointPlus]
        nlinarith [sq_nonneg (s - 1)]
      adjoint_dde := by
        intro s _hs
        exact section13AdjointPlus_dde s
      pairing_zero := by
        intro s hs
        have hz := section13Qhat_pairing_zero hH hs
        have heq := sub_eq_zero.mp hz
        simpa [section10SignedPairing, section13AdjointPlus] using heq }
  have hadj : h.adjoint = explicitKappaOneAdjointPlus := by
    funext s
    rfl
  let M := section10_plus_commonMajorant_internal h hadj (by norm_num)
    (le_rfl : Real.exp 2 + 1 ≤ Real.exp 2 + 1)
    (section13Qhat_normalizedPlusSlope_bddBelow hH)
  refine ⟨M.cPlus, M.cutoff, M.one_le_cPlus, ?_, M.four_le_cutoff, M.envelope_slope_nonneg⟩
  have : Real.exp 2 + 1 ≤ M.cutoff := by
    dsimp [M]
    exact le_rfl
  linarith


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
