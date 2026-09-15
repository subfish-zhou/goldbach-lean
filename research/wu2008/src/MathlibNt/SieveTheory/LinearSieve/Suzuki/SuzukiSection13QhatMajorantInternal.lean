import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1027ExplicitAdjoint
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1056UniformStationary
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13MajorantsFinal

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1200000

open BridgeAssembly CutoffCorrectedRatio
open Section10Lemma1028FirstCrossing
open Section10CanonicalXi
open Section10Equation1056UniformStationary
open Section13QhatMajorantClosure
open Section13MajorantsFinal

lemma section13Qhat_normalizedMinusBase_continuousOn_compact
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) (S : ℝ) :
    ContinuousOn (normalizedMinusBase (section13Qhat H) xi) (Icc 3 S) := by
  intro s hs
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs.1
  have hs0 : s ≠ 0 := ne_of_gt hspos
  have hsm0 : 0 < s - 1 := by linarith [hs.1]
  have hQs : 0 < section13Qhat H s :=
    section13Qhat_pos hH.toSection13HatContract hspos
  have hQc : ContinuousAt (section13Qhat H) s :=
    (section13Qhat_continuousOn hH.toSection13HatContract).continuousAt
      (Ioi_mem_nhds hspos)
  have hQmc : ContinuousAt (fun u : ℝ => section13Qhat H (u - 1)) s :=
    ((section13Qhat_continuousOn hH.toSection13HatContract).continuousAt
      (Ioi_mem_nhds hsm0)).comp_of_eq
        (continuousAt_id.sub continuousAt_const) (by simp)
  exact (((hQmc.neg.div (continuousAt_id.mul hQc)
    (mul_ne_zero hs0 (ne_of_gt hQs))).add xi_continuous.continuousAt).sub
      (continuousAt_const.div continuousAt_id hs0)).continuousWithinAt

noncomputable def section13Qhat_minusMajorant_internal
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    QhatMinusMajorant (section13Qhat H) := by
  let h := section13QhatFirstCrossingData hH
  let h27 := section13Qhat_lemma1027AdjointRComparison hH
  exact qhatMinusMajorant_of_uniform_stationary h rfl h27 (by norm_num)
    (section13Qhat_normalizedMinusBase_continuousOn_compact hH (stationaryCutoff h27))

noncomputable def section13Qhat_cutoffMajorant_internal
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    CutoffMajorant (section13Qhat H) := by
  let Q := section13Qhat_minusMajorant_internal hH
  exact
    { xi := xi
      cMinus := Q.cMinus
      cutoff := Q.cutoff
      A := Q.A
      four_le_cutoff := Q.four_le_cutoff
      one_le_A := Q.one_le_A
      majorizes_log := Q.majorizes_log
      envelope_slope_nonpos := Q.envelope_slope_nonpos }

/-- Fully internalized moving Claim 14.6(iii): the only mathematical input is
Section 13's source contract, including its genuine (T5) exponential decay. -/
theorem moving_claim14_6_iii_of_section13HatSourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {d Δ : ℝ} (hd : 0 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    Section13MajorantsFinal.MovingClaim146iiiConclusion H d Δ := by
  exact moving_claim14_6_iii_of_singleQhatMajorant hH hd hΔ0 hΔ1
    (section13Qhat_cutoffMajorant_internal hH)


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
