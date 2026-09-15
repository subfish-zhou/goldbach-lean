import SigmaVariableInnerFTC

noncomputable section
namespace SigmaVariableFull
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open Wu04WholeCollection OriginalSigmaStrength ActualNineFeedback
open scoped Interval BigOperators

/-- The complete inner mass, retaining the original logarithms and every pole. -/
def endpointMass (t : ℝ) : ℝ :=
  -D0FullDensity.zeroPrimitive 1+TerminalE.primitive (-(t+1)) 1+
    D0FullDensity.zeroPrimitive ((t+1)/2)-TerminalE.primitive (-(t+1)) ((t+1)/2)

theorem endpointMass_eq {t : ℝ} (ht : t ∈ Icc 1 3) : endpointMass t=innerMass t :=
  (innerMass_endpoints ht).symm

theorem endpointMass_continuousAt {t : ℝ} (ht : t ∈ Icc 1 3) :
    ContinuousAt endpointMass t := by
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have ht1 : t+1 ≠ 0 := by linarith [ht.1]
  have hp : -(t+1) ≠ 0 := neg_ne_zero.mpr ht1
  have hp1 : -(t+1)+1 ≠ 0 := by linarith [ht.1]
  have hq : TerminalE.q (-(t+1)) ≠ 0 := (pole_quadratic ht).ne
  have hr : TerminalE.radical ≠ 0 := TerminalE.radical_pos.ne'
  have hx : 1 ≤ (t+1)/2 := by linarith [ht.1]
  have hm : 0 < (t+1)/2+4-TerminalE.radical := by
    linarith [TerminalE.radical_lt_four]
  have hm1 : 0 < 1+4-TerminalE.radical := by
    linarith [TerminalE.radical_lt_four]
  have htpos : 0<t := by linarith [ht.1]
  unfold endpointMass D0FullDensity.zeroPrimitive TerminalE.primitive
    TerminalE.quadraticPrimitive FirstCRationalPayment.polePrimitive
    TerminalE.mainCoeff TerminalE.zeroOne TerminalE.zeroTwo TerminalE.negOne
    TerminalE.negTwo TerminalE.negThree TerminalE.negFour TerminalE.quadOne
    TerminalE.quadZero TerminalE.residue
  unfold TerminalE.q at hq ⊢
  simp only [sub_zero,sub_neg_eq_add]
  fun_prop (disch := first | assumption | positivity | linarith [TerminalE.radical_pos])

def weight (t : ℝ) : ℝ := endpointMass t/t

theorem weight_continuous : ContinuousOn weight (uIcc (1:ℝ) 3) := by
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
  intro t ht
  exact ((endpointMass_continuousAt ht).div continuousAt_id
    (by change t ≠ 0; linarith [ht.1])).continuousWithinAt

theorem old_weight_le {t : ℝ} (ht : t ∈ Icc 1 3) :
    SigmaInnerProfile.weight t ≤ weight t := by
  rw [weight,endpointMass_eq ht,innerMass_balance ht]
  unfold SigmaInnerProfile.weight
  exact div_le_div_of_nonneg_right
    (le_add_of_nonneg_right (CorrectionSigmaVariable.variationMass_nonneg ht.1))
    (by linarith [ht.1])

theorem weight_le_sigma {t : ℝ} (ht : t ∈ Icc 1 3) :
    weight t ≤ sigma 3 (t+2) (t+1)/t := by
  rw [weight,endpointMass_eq ht]
  exact div_le_div_of_nonneg_right (innerMass_le_sigma ht) (by linarith [ht.1])

/-- Exact original nine cells; these are not yet finite scalar certificates. -/
def cellMass (a b : ℝ) : ℝ := ∫ t in a..b,weight t
def numerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9,z k*cellMass (upperLeft k) (upperNode k)

theorem numerator_integral (z : Fin 9 → ℝ) :
    numerator z=∫ t in (1:ℝ)..3,nineProfile z t*weight t := by
  rw [profile_integral_cells z le_rfl (by norm_num [upperNode]) weight_continuous]
  apply Finset.sum_congr rfl
  intro k _
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he]
  rfl

theorem old_numerator_le {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) :
    SigmaInnerProfile.numerator z ≤ numerator z := by
  rw [SigmaInnerProfile.numerator_integral,numerator_integral]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((nineProfile_integrable z).mul_continuousOn
      (SigmaInnerProfile.weight_continuous (by norm_num) (by norm_num)))
    ((nineProfile_integrable z).mul_continuousOn weight_continuous)
  intro t ht
  exact mul_le_mul_of_nonneg_left (old_weight_le ht) (nineProfile_nonneg hz t)

def profile (z : Fin 9 → ℝ) : ℝ := numerator z/(1-D0FullDensity.finiteD)

theorem profile_le_actual :
    profile NineFeedbackStrength.originalH ≤ aProfile (nineProfile NineFeedbackStrength.originalH) := by
  have hz := CoupledIntegralRecovery.originalH_nonneg
  have hn : 0 ≤ numerator NineFeedbackStrength.originalH :=
    SigmaInnerProfile.original_numerator_pos.le.trans (old_numerator_le hz)
  apply le_trans (b := numerator NineFeedbackStrength.originalH/(1-D0))
  · exact div_le_div_of_nonneg_left hn (sub_pos.mpr D0_lt_one)
      (by linarith only [D0FullDensity.finiteD_le_D0])
  rw [aProfile_eq,numerator_integral]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0_lt_one).le
  have hp := nineProfile_integrable NineFeedbackStrength.originalH
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hp.mul_continuousOn weight_continuous)
    ((profile_div_integrable hp).mul_continuousOn original_sigma_continuous)
  intro t ht
  have h := mul_le_mul_of_nonneg_left (weight_le_sigma ht) (nineProfile_nonneg hz t)
  convert h using 1 <;> first | rfl | skip
  ring

theorem old_profile_le : CorrectionD0Joint.profile ≤ profile NineFeedbackStrength.originalH := by
  exact div_le_div_of_nonneg_right
    (CorrectionD0Joint.numerator_le.trans (old_numerator_le CoupledIntegralRecovery.originalH_nonneg))
    (sub_pos.mpr D0FullDensity.finiteD_lt_one).le

def terminal : ℝ := log 2*profile NineFeedbackStrength.originalH+
  TerminalESigned.massPaid NineFeedbackStrength.originalH

theorem terminal_le_actual : terminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have ha := mul_le_mul_of_nonneg_left profile_le_actual
    (log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  have he := TerminalESigned.massPaid_le CoupledIntegralRecovery.originalH_nonneg
  have hm := TerminalECells.mass_le CoupledIntegralRecovery.originalH_nonneg
  unfold terminal
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [ha,he,hm]

theorem old_terminal_le : CorrectionD0Joint.terminal ≤ terminal := by
  have hl := mul_le_mul_of_nonneg_right (RemainingHf.splitLower_le (by norm_num : (1:ℝ) ≤ 2))
    CorrectionD0Joint.profile_pos.le
  have hp := mul_le_mul_of_nonneg_left old_profile_le (log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  unfold CorrectionD0Joint.terminal terminal
  linarith only [hl,hp]

end SigmaVariableFull
