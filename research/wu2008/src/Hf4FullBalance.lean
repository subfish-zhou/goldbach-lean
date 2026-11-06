import Hf4FullProfile

noncomputable section
namespace Hf4Full
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback

/-- Unpaid outer log-envelope loss. This is NOT a new finite payment. -/
def outerUnpaid : ℝ := SigmaVariableFull.numerator NineFeedbackStrength.originalH -
  SigmaActualBlockSeparable.endpointNumerator NineFeedbackStrength.originalH

theorem outerUnpaid_nonneg : 0 ≤ outerUnpaid := by
  unfold outerUnpaid
  rw [SigmaActualBlockSeparable.endpointNumerator_eq_rational]
  exact sub_nonneg.mpr (SigmaVariableOuterPayment.rationalNumerator_le CoupledIntegralRecovery.originalH_nonneg)

/-- The independent newVariation cancels exactly; it is not part of the outer loss. -/
theorem numerator_endpoint_balance : numerator = endpointNumerator + outerUnpaid := by
  unfold numerator endpointNumerator outerUnpaid
  ring

theorem profile_endpoint_balance : profile = endpointProfile + outerUnpaid/(1-D0FullDensity.dPaid) := by
  unfold profile endpointProfile
  rw [numerator_endpoint_balance, add_div]

theorem terminal_endpoint_balance : terminal = endpointTerminal +
    log 2*outerUnpaid/(1-D0FullDensity.dPaid) := by
  unfold terminal endpointTerminal
  rw [profile_endpoint_balance]
  ring

/-- Exact certificate improvement; integral-defined, not a computed endpoint gain. -/
def recoveredNumerator : ℝ := numerator-Hf4Den.numerator



/-- Still owed after full-variable plus independent log residual. -/
def numeratorUnpaid : ℝ :=
  (∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t/t*sigma 3 (t+2) (t+1))-numerator

theorem numeratorUnpaid_nonneg : 0 ≤ numeratorUnpaid := sub_nonneg.mpr numerator_le_actual


/-- The true D0-minus-dPaid account is reused without changing D0 or its original max. -/
def profileUnpaid : ℝ := numeratorUnpaid/(1-D0)+
  numerator*Hf4Den.dUnpaid/((1-D0)*(1-D0FullDensity.dPaid))

theorem profileUnpaid_nonneg : 0 ≤ profileUnpaid :=
  add_nonneg (div_nonneg numeratorUnpaid_nonneg (sub_pos.mpr D0_lt_one).le)
    (div_nonneg (mul_nonneg numerator_pos.le Hf4Den.dUnpaid_nonneg)
      (mul_pos (sub_pos.mpr D0_lt_one) (sub_pos.mpr D0FullDensity.dPaid_lt_one)).le)

theorem actual_profile_balance : aProfile (nineProfile NineFeedbackStrength.originalH) =
    profile+profileUnpaid := by
  have hD := (sub_pos.mpr D0_lt_one).ne'
  have hd := (sub_pos.mpr D0FullDensity.dPaid_lt_one).ne'
  rw [aProfile_eq]
  unfold profile profileUnpaid numeratorUnpaid Hf4Den.dUnpaid
  field_simp
  ring

/-- E endpoint loss is already consumed once; only original intrinsicEUnpaid remains. -/
def remaining : ℝ := log 2*profileUnpaid + CorrectionD0Joint.intrinsicEUnpaid

theorem remaining_nonneg : 0 ≤ remaining :=
  add_nonneg (mul_nonneg (log_nonneg (by norm_num : (1:ℝ)≤2)) profileUnpaid_nonneg)
    CorrectionD0Joint.intrinsicEUnpaid_nonneg

theorem actual_terminal_balance : firstFeedback NineFeedbackStrength.originalH 3 3 =
    terminal+remaining := by
  unfold terminal remaining CorrectionD0Joint.intrinsicEUnpaid
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  rw [actual_profile_balance]
  ring


theorem original_unpaid_balance : CorrectionD0Joint.allUnpaid =
    (terminal-CorrectionD0Joint.terminal)+remaining := by
  have ho := CorrectionD0Joint.actual_terminal_balance
  have hn := actual_terminal_balance
  linarith only [ho,hn]

/-- Endpoint account must additionally owe the uncomputed outer envelope loss. -/
def endpointRemaining : ℝ := log 2*outerUnpaid/(1-D0FullDensity.dPaid)+remaining


theorem actual_endpoint_terminal_balance : firstFeedback NineFeedbackStrength.originalH 3 3 =
    endpointTerminal+endpointRemaining := by
  rw [actual_terminal_balance,terminal_endpoint_balance]
  unfold endpointRemaining
  ring


/-- Exact original obligation, not the stronger sufficient lower-terminal test. -/
theorem original_hf4_iff_remaining :
    (NineFeedbackStrength.originalH 8 ≤ firstFeedback NineFeedbackStrength.originalH 3 3) ↔
      NineFeedbackStrength.originalH 8-terminal ≤ remaining := by
  rw [actual_terminal_balance]
  exact (sub_le_iff_le_add').symm


end Hf4Full
