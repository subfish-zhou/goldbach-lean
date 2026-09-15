import SigmaSignedInnerIntegral
namespace SigmaSignedCells
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals
open scoped Interval BigOperators
noncomputable section

/-- Unliquidated original-nine-cell rational mass; not claimed to be a finite payment. -/
def correctionNumerator : ℝ := ∑ k : Fin 9,NineFeedbackStrength.originalH k*
  correctionMass (upperLeft k) (upperNode k)

theorem correctionNumerator_nonneg : 0 ≤ correctionNumerator := by
  apply Finset.sum_nonneg
  intro k _
  have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he] at hb
  exact mul_nonneg (CoupledIntegralRecovery.originalH_nonneg k)
    (correctionMass_nonneg hb.1 hb.2.1 hb.2.2.1)

theorem correctedNumerator_le : numerator NineFeedbackStrength.originalH+correctionNumerator ≤
    SigmaInnerProfile.numerator NineFeedbackStrength.originalH := by
  unfold numerator correctionNumerator SigmaInnerProfile.numerator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he] at hb
  simpa only [mul_add] using mul_le_mul_of_nonneg_left
    (correctedCell_le hb.1 hb.2.1 hb.2.2.1) (CoupledIntegralRecovery.originalH_nonneg k)

def correctedProfile : ℝ := max (SigmaRemaining.finiteLower NineFeedbackStrength.originalH)
  (finiteLower+correctionNumerator/(1-SigmaRemaining.d0Paid))

theorem correctedProfile_le_inner : correctedProfile ≤
    SigmaInnerProfile.d0Lower NineFeedbackStrength.originalH := by
  apply max_le SigmaInnerProfile.old_finiteLower_le
  have h := div_le_div_of_nonneg_right correctedNumerator_le
    (sub_pos.mpr SigmaRemaining.d0Paid_lt_one).le
  simpa only [add_div,finiteLower,SigmaInnerProfile.d0Lower] using h

theorem correctedProfile_le : correctedProfile ≤
    aProfile (nineProfile NineFeedbackStrength.originalH) :=
  correctedProfile_le_inner.trans SigmaInnerProfile.original_d0Lower_le_profile

theorem profileLower_le_corrected : profileLower ≤ correctedProfile := by
  apply max_le_max le_rfl
  exact le_add_of_nonneg_right (div_nonneg correctionNumerator_nonneg
    (sub_pos.mpr SigmaRemaining.d0Paid_lt_one).le)

/-- Same actual four rows and complete E/J/middle/density, with a genuine unpaid integral retained. -/
def correctedCoupledLower (p : Wu2008DoubleSieve.SecondFunctionalParameters) : ℝ :=
  coupledLower p+CoupledFiniteAssembly.aCoefficient p*(correctedProfile-profileLower)

theorem correctedCoupledLower_le (i : Fin 4) : correctedCoupledLower (ActualNineFeedback.coupledRow i) ≤
    ActualNineFeedback.coupledFeedback (ActualNineFeedback.coupledRow i) NineFeedbackStrength.originalH := by
  have hm := mul_le_mul_of_nonneg_left correctedProfile_le_inner
    (CoupledFiniteAssembly.aCoefficient_nonneg (ActualNineFeedback.coupledRow_geometry i))
  have hc := SigmaInnerProfile.coupledLower_le_original i
  unfold correctedCoupledLower coupledLower SigmaInnerProfile.coupledLower at *
  linarith only [hm,hc]

theorem coupledLower_le_corrected (i : Fin 4) : coupledLower (ActualNineFeedback.coupledRow i) ≤
    correctedCoupledLower (ActualNineFeedback.coupledRow i) := by
  apply le_add_of_nonneg_right
  exact mul_nonneg (CoupledFiniteAssembly.aCoefficient_nonneg (ActualNineFeedback.coupledRow_geometry i))
    (sub_nonneg.mpr profileLower_le_corrected)

end
end SigmaSignedCells
