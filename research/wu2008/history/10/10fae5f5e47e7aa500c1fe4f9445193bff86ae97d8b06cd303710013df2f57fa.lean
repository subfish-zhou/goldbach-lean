import E10FourRebate

noncomputable section
open Real Wu2008DoubleSieve Wu08OriginalFourWeights
open ClassicalLogFourBounds WuTarget.W13

namespace WuTarget.E10Four

def recovery : ℝ := (36/5)*rebateCoeff*FourLogAffine.l^4/12
def pairUpper : ℝ := W13Tight.pairUpper-recovery
def netCredit : ℝ := recovery/4

theorem recovery_pos : 0 < recovery := by
  have hl := FourLogAffine.fixed_log_bounds.1
  have hc := rebateCoeff_pos
  unfold recovery
  positivity

theorem recovery_paid :
    recovery ≤ (36/5)*(∫ x in FourRoughClosedMass.alpha..FourRoughClosedMass.beta,
      rebate x) := by
  rw [rebate_integral]
  have hp := pow_le_pow_left₀ FourLogAffine.fixed_log_bounds.1.le
    FourLogAffine.fixed_log_bounds.2.1 4
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (36/5)*rebateCoeff/12 from by
      have hc := rebateCoeff_pos
      positivity)
  unfold recovery
  ring_nf at hm ⊢
  exact hm

theorem original_pair_upper :
    original10+original11 ≤ pairUpper := by
  have h2 := mul_le_mul_of_nonneg_left (W13Tight.moment_upper 2)
    coefficients_positive.2.1.le
  have h3 := mul_le_mul_of_nonneg_left (W13Tight.moment_upper 3)
    coefficients_positive.2.2.1.le
  have h4 := mul_le_mul_of_nonneg_left (W13Tight.moment_upper 4)
    coefficients_positive.2.2.2.le
  have hm := original_pair_rebate.trans (add_le_add (add_le_add h2 h3) h4)
  change original10+original11+(36/5)*(∫ x in
    FourRoughClosedMass.alpha..FourRoughClosedMass.beta, rebate x) ≤
      W13Tight.pairUpper at hm
  unfold pairUpper
  linarith only [hm,recovery_paid]

theorem pair_strict : pairUpper < W13Tight.pairUpper := by
  unfold pairUpper
  linarith only [recovery_pos]

theorem netCredit_pos : 0 < netCredit := div_pos recovery_pos (by norm_num)

theorem exact_recovery : W13Tight.pairUpper-pairUpper = recovery := by
  unfold pairUpper
  ring

theorem net_identity :
    (original10+original11-pairUpper)/4 =
      (original10+original11-W13Tight.pairUpper)/4+netCredit := by
  unfold pairUpper netCredit
  ring

#print Wu2008DoubleSieve.truncatedSixthLowerAlpha
#print Wu2008DoubleSieve.truncatedSixthLowerBeta
#print Wu2008DoubleSieve.truncatedSixthLowerLambda

end WuTarget.E10Four
