import SrcFourEnvelope

noncomputable section
open Wu2008DoubleSieve FourRoughClosedMass WuTarget.E10FourMajor
open Wu08OriginalFourWeights

namespace WuSource.SrcFour

theorem tailCap_nonneg : 0 ≤ tailCap := by
  have hl : 0 ≤ tailLogCap := tail_log_bounds.1.trans tail_log_bounds.2
  unfold tailCap
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  have ha := (coefficients_pos i).1
  have hb := (coefficients_pos i).2
  positivity

theorem tailCap_small : tailCap < (1/1000 : ℝ) := by
  norm_num [tailCap,tailLogCap,outerCut,coefA,coefB,Fin.sum_univ_succ,
    recipCoeff,crossCap,slope,z0,SharpLogRecurrence.upperLog,SharpLogRecurrence.lowerLog,
    alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem fineCap_5616_upper : fineCap (351/625) < (86/125 : ℝ) := by
  have hp := mul_le_mul_of_nonneg_left pairCap_lt_target.le
    (by norm_num [scale] : 0 ≤ scale (351/625))
  have ht := mul_le_mul_of_nonneg_left tailCap_small.le
    (by norm_num [scale] : 0 ≤ 1-scale (351/625))
  norm_num [scale] at hp ht
  unfold fineCap scale
  linarith only [hp,ht]

theorem scaled_parentCap_exceeds_target :
    (13/20 : ℝ) < scale (351/625)*pairCap := by
  norm_num [scale,pairCap,capTerm,Fin.sum_univ_succ,recipCoeff,crossCap,slope,z0,
    WuTarget.W13Tight.momentUpper,WuTarget.W13Tight.discount,WuTarget.W13Tight.primitive,
    WuTarget.W13.h,WuTarget.W13.d,WuTarget.W13.k,WuTarget.W13.cut,FourLogAffine.u,
    SharpLogRecurrence.upperLog,SharpLogRecurrence.lowerLog,
    alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem fineCap_5616_exceeds_target : (13/20 : ℝ) < fineCap (351/625) := by
  have ht := mul_nonneg (by norm_num [scale] : 0 ≤ 1-scale (351/625)) tailCap_nonneg
  unfold fineCap
  linarith only [scaled_parentCap_exceeds_target,ht]

theorem original_pair_5616_conditional
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ 351/625) :
    original10+original11 < (86/125 : ℝ) :=
  (original_pair_fineCap (by norm_num) (by norm_num) hc).trans_lt fineCap_5616_upper

theorem conditional_budget_difference :
    ((7/10 : ℝ)-86/125)/4 = 3/1000 ∧
      ((86/125 : ℝ)-13/20)/4 = 19/2000 := by norm_num

#check @tailCap_small
#check @fineCap_5616_upper
#check @fineCap_5616_exceeds_target
#check @original_pair_5616_conditional
#check @conditional_budget_difference
#print axioms tailCap_small
#print axioms fineCap_5616_upper
#print axioms fineCap_5616_exceeds_target
#print axioms original_pair_5616_conditional
#print axioms conditional_budget_difference
end WuSource.SrcFour
