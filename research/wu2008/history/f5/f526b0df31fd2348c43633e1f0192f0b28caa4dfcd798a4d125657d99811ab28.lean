import R2OmegaHighNormalize
import MathlibNt.Wu2008DoubleSieve.HighSixPrimeDeltaLimit

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle
open Finset Real Set
open scoped Classical Topology Interval BigOperators

def previousNode (j : Fin 4) : ℝ := sourceNode (5 + j.val)
def paperCoefficient (j : Fin 4) : ℝ :=
  8 * ∫ t in ((1 / 2 - psiRight (index j)) / truncatedSixthLowerAlpha)..psiNode (index j),
    (wuUpperCoefficient t - firstFunctionalGainPsiOne (psiNode (index j)) (psiTop (index j))) /
      (t * (1 - 2 * truncatedSixthLowerAlpha * t))

theorem window_endpoints (j : Fin 4) :
    (1 / 10 : ℝ) ≤ psiLeft (index j) ∧
    0 < previousNode j ∧ previousNode j ≤ psiNode (index j) ∧
    1 / 2 - truncatedSixthLowerAlpha * previousNode j = psiRight (index j) ∧
    (1 / 2 - psiRight (index j)) / truncatedSixthLowerAlpha = previousNode j ∧
    psiLogWeight (index j) = sourceWeight (previousNode j) (psiNode (index j)) := by
  fin_cases j <;> norm_num [previousNode, index, Fin.natAdd, psiLeft, psiRight,
    psiNode, psiLogWeight, sourceNode, truncatedSixthLowerAlpha]

theorem initial_upper {t : ℝ} (ht : 0 < t) (ht3 : t ≤ 3) : wuUpperCoefficient t = 1 := by
  unfold wuUpperCoefficient
  rw [MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965F_eq_of_le_three ht3]
  field_simp [ht.ne', (exp_pos eulerMascheroniConstant).ne']

theorem outer_integral_zero (j : Fin 4) : outerIntegral j 0 = 2 * psiLogWeight (index j) := by
  have hg := window_endpoints j
  have hs3 := (geometry j).2.1
  have ha : truncatedSixthLowerAlpha ≠ 0 := by norm_num [truncatedSixthLowerAlpha]
  let f : ℝ → ℝ := fun t => 1 / (t * (1 / 2 - t))
  have hchange := intervalIntegral.integral_comp_sub_mul f
    (a := previousNode j) (b := psiNode (index j)) ha (1 / 2)
  rw [hg.2.2.2.1, show 1 / 2 - truncatedSixthLowerAlpha * psiNode (index j) =
    psiLeft (index j) from rfl, smul_eq_mul] at hchange
  have hmul := congrArg (fun x : ℝ => truncatedSixthLowerAlpha * x) hchange
  rw [← intervalIntegral.integral_const_mul] at hmul
  have heq : (∫ t in previousNode j..psiNode (index j),
      truncatedSixthLowerAlpha * f (1 / 2 - truncatedSixthLowerAlpha * t)) =
        2 * psiLogWeight (index j) := by
    rw [hg.2.2.2.2.2, ← source_kernel_integral hg.2.1 hg.2.2.1
      (show psiNode (index j) ≤ 49 / 10 by linarith), ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hg.2.2.1] at ht
    have ht0 : t ≠ 0 := (hg.2.1.trans_le ht.1).ne'
    have ht3 : t ≤ 3 := ht.2.trans hs3
    have hden : 1 - 2 * truncatedSixthLowerAlpha * t ≠ 0 := by
      norm_num [truncatedSixthLowerAlpha]
      linarith
    have hhalf : 1 / 2 - truncatedSixthLowerAlpha * t ≠ 0 := by
      norm_num [truncatedSixthLowerAlpha]
      linarith
    dsimp [f, sourceKernel]
    rw [show 1 / 2 - (1 / 2 - truncatedSixthLowerAlpha * t) = truncatedSixthLowerAlpha * t by ring]
    field_simp
    <;> ring
  rw [heq, ← mul_assoc, mul_inv_cancel₀ ha, one_mul] at hmul
  simpa only [outerIntegral, sub_zero, f] using hmul.symm

theorem paper_coefficient_log (j : Fin 4) :
    paperCoefficient j =
      8 * (1 - firstFunctionalGainPsiOne (psiNode (index j)) (psiTop (index j))) *
        psiLogWeight (index j) := by
  have hg := window_endpoints j
  have hs3 := (geometry j).2.1
  rw [paperCoefficient, hg.2.2.2.2.1, hg.2.2.2.2.2,
    ← source_kernel_integral hg.2.1 hg.2.2.1 (show psiNode (index j) ≤ 49 / 10 by linarith)]
  rw [mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hg.2.2.1] at ht
  dsimp only
  rw [initial_upper (hg.2.1.trans_le ht.1) (ht.2.trans hs3)]
  unfold sourceKernel
  ring

theorem psi_zero_eq_source (j : Fin 4) :
    firstFunctionalGainPsi 0 (psiNode (index j)) (psiTop (index j)) =
      firstFunctionalGainPsiOne (psiNode (index j)) (psiTop (index j)) := by
  have hg := geometry j
  simpa only [mul_zero, sub_zero, zero_div, zero_mul] using
    firstFunctionalGainPsi_eq_source_sub_penalty (δ := 0) (by norm_num)
      hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1

theorem fixed_zero_eq_paper (j : Fin 4) : fixedCoefficient j 0 = paperCoefficient j := by
  rw [fixedCoefficient, psi_zero_eq_source, outer_integral_zero, paper_coefficient_log]
  ring

#check @WuPaper.R2OmegaHigh.previousNode
#check @WuPaper.R2OmegaHigh.paperCoefficient
#check @WuPaper.R2OmegaHigh.window_endpoints
#check @WuPaper.R2OmegaHigh.initial_upper
#check @WuPaper.R2OmegaHigh.outer_integral_zero
#check @WuPaper.R2OmegaHigh.paper_coefficient_log
#check @WuPaper.R2OmegaHigh.psi_zero_eq_source
#check @WuPaper.R2OmegaHigh.fixed_zero_eq_paper
#print axioms WuPaper.R2OmegaHigh.previousNode
#print axioms WuPaper.R2OmegaHigh.paperCoefficient
#print axioms WuPaper.R2OmegaHigh.window_endpoints
#print axioms WuPaper.R2OmegaHigh.initial_upper
#print axioms WuPaper.R2OmegaHigh.outer_integral_zero
#print axioms WuPaper.R2OmegaHigh.paper_coefficient_log
#print axioms WuPaper.R2OmegaHigh.psi_zero_eq_source
#print axioms WuPaper.R2OmegaHigh.fixed_zero_eq_paper
end WuPaper.R2OmegaHigh
