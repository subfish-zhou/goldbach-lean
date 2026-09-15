import SigmaCorrectionCollected
namespace SigmaCorrectionFTC
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals
open SigmaSignedCells
open scoped Interval BigOperators
noncomputable section

theorem original_cell_bounds (k : Fin 9) :
    1≤upperLeft k ∧ upperLeft k≤upperNode k ∧ upperNode k≤3 := by
  have h := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he] at h
  exact ⟨h.1,h.2.1,h.2.2.1⟩

/-- All original nine cells, not a sampled or shortened domain. -/
theorem original_nine_correction_ftc (k : Fin 9) :
    correctionMass (upperLeft k) (upperNode k)=primitive (upperNode k)-primitive (upperLeft k) :=
  correctionMass_ftc (original_cell_bounds k).1 (original_cell_bounds k).2.1

def correctionEndpoints : ℝ := ∑ k : Fin 9,NineFeedbackStrength.originalH k*
  (primitive (upperNode k)-primitive (upperLeft k))

theorem correctionNumerator_endpoints : correctionNumerator=correctionEndpoints := by
  unfold correctionNumerator correctionEndpoints
  apply Finset.sum_congr rfl
  intro k _
  rw [original_nine_correction_ftc k]

/-- Literal identity for the parent's same corrected profile and unchanged denominator. -/
theorem correctedProfile_endpoints : correctedProfile=
    max (SigmaRemaining.finiteLower NineFeedbackStrength.originalH)
      (SigmaSignedCells.finiteLower+correctionEndpoints/(1-SigmaRemaining.d0Paid)) := by
  rw [correctedProfile,correctionNumerator_endpoints]

theorem fullCell_identity {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    fullPrimitive b-fullPrimitive a=
      SigmaPrimitiveCells.cellMass a b+correctionMass a b := by
  rw [correctionMass_ftc ha hab,fullPrimitive_identity a,fullPrimitive_identity b]
  unfold SigmaPrimitiveCells.cellMass
  ring

theorem fullCell_le_inner {a b : ℝ} (ha : 1≤a) (hab : a≤b) (hb : b≤3) :
    fullPrimitive b-fullPrimitive a≤SigmaInnerProfile.cellIntegral a b := by
  have hi : IntervalIntegrable SigmaInnerPaid.weight volume a b :=
    (SigmaInnerPaid.weight_continuous (by linarith) hab).intervalIntegrable
  have hj : IntervalIntegrable correctionWeight volume a b :=
    (correctionWeight_continuous (by linarith) hab).intervalIntegrable
  have hm : (∫ t in a..b,SigmaInnerPaid.weight t+correctionWeight t)≤
      SigmaInnerProfile.cellIntegral a b := by
    apply intervalIntegral.integral_mono_on hab (hi.add hj)
      (SigmaInnerProfile.weight_continuous (by linarith) hab).intervalIntegrable
    intro t ht
    have h := div_le_div_of_nonneg_right
      (innerCorrection_le_gap (ha.trans ht.1) (ht.2.trans hb)) (by linarith [ht.1] : 0≤t)
    simpa only [add_div,SigmaInnerPaid.weight,correctionWeight,SigmaInnerProfile.weight] using h
  rw [intervalIntegral.integral_add hi hj,SigmaInnerPaid.weight_integral ha hab] at hm
  rw [fullCell_identity ha hab]
  exact hm

def fullNumerator : ℝ := ∑ k : Fin 9,NineFeedbackStrength.originalH k*
  fullCellPaid (upperLeft k) (upperNode k)

theorem fullNumerator_le_inner : fullNumerator≤
    SigmaInnerProfile.numerator NineFeedbackStrength.originalH := by
  apply Finset.sum_le_sum
  intro k _
  obtain ⟨ha,hab,hb⟩ := original_cell_bounds k
  exact mul_le_mul_of_nonneg_left ((fullCellPaid_le ha hab).trans (fullCell_le_inner ha hab hb))
    (CoupledIntegralRecovery.originalH_nonneg k)

/-- Same common profile, old maximum retained, old d0Paid unchanged. Only the numerator changes. -/
def finiteProfile : ℝ := max SigmaSignedCells.profileLower
  (fullNumerator/(1-SigmaRemaining.d0Paid))

theorem finiteProfile_le_inner : finiteProfile≤
    SigmaInnerProfile.d0Lower NineFeedbackStrength.originalH := by
  apply max_le
  · exact SigmaSignedCells.profileLower_le_corrected.trans SigmaSignedCells.correctedProfile_le_inner
  · exact div_le_div_of_nonneg_right fullNumerator_le_inner
      (sub_pos.mpr SigmaRemaining.d0Paid_lt_one).le

theorem finiteProfile_le : finiteProfile≤aProfile (nineProfile NineFeedbackStrength.originalH) :=
  finiteProfile_le_inner.trans SigmaInnerProfile.original_d0Lower_le_profile

theorem old_profile_le_finite : SigmaSignedCells.profileLower≤finiteProfile := le_max_left _ _

def coupledLower (p : Wu2008DoubleSieve.SecondFunctionalParameters) : ℝ :=
  SigmaSignedCells.coupledLower p+CoupledFiniteAssembly.aCoefficient p*
    (finiteProfile-SigmaSignedCells.profileLower)

theorem coupledLower_le_actual (i : Fin 4) : coupledLower (ActualNineFeedback.coupledRow i)≤
    ActualNineFeedback.coupledFeedback (ActualNineFeedback.coupledRow i) NineFeedbackStrength.originalH := by
  have h := mul_le_mul_of_nonneg_left finiteProfile_le_inner
    (CoupledFiniteAssembly.aCoefficient_nonneg (ActualNineFeedback.coupledRow_geometry i))
  have hc := SigmaInnerProfile.coupledLower_le_original i
  unfold coupledLower SigmaSignedCells.coupledLower SigmaInnerProfile.coupledLower at *
  linarith only [h,hc]

theorem old_coupled_le_finite (i : Fin 4) : SigmaSignedCells.coupledLower (ActualNineFeedback.coupledRow i)≤
    coupledLower (ActualNineFeedback.coupledRow i) := by
  apply le_add_of_nonneg_right
  exact mul_nonneg (CoupledFiniteAssembly.aCoefficient_nonneg (ActualNineFeedback.coupledRow_geometry i))
    (sub_nonneg.mpr old_profile_le_finite)

/-- The literal complete four-row expression with all inherited E/J/middle/density terms. -/
theorem coupledLower_collected (p : Wu2008DoubleSieve.SecondFunctionalParameters) : coupledLower p=
    CoupledFiniteAssembly.aCoefficient p*finiteProfile+
      (4*ResidualEndpointJoint.eRest NineFeedbackStrength.originalH p.S+
        ResidualEndpointJoint.eRest NineFeedbackStrength.originalH p.kappa1+
        SigmaJEndpoint.endpointRest NineFeedbackStrength.originalH p.s p.S+
        SigmaJEndpoint.endpointRest NineFeedbackStrength.originalH p.kappa2 p.S+
        SigmaJEndpoint.endpointRest NineFeedbackStrength.originalH p.kappa3 p.S+
        GatedDensityPayment.densityFinite p NineFeedbackStrength.originalH+
        NineFeedbackStrength.originalH 0*CoupledHGateRecovery.gatePayment p+
        NineFeedbackStrength.originalH 0*CoupledMiddleGateRecovery.middleGain p)/5 := by
  unfold coupledLower
  rw [SigmaSignedCells.coupledLower_collected]
  ring

end
end SigmaCorrectionFTC
