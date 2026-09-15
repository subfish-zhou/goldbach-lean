import Hf4DenProfile

noncomputable section
namespace Hf4Den
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback

/-- Still unpaid: the actual numerator integral minus the unchanged latest certificate. -/
def numeratorUnpaid : ℝ :=
  (∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t/t*sigma 3 (t+2) (t+1))-numerator

theorem numeratorUnpaid_nonneg : 0 ≤ numeratorUnpaid := sub_nonneg.mpr numerator_le_actual

/-- Still unpaid: the true D0, not its already paid full-density primitive. -/
def dUnpaid : ℝ := D0-D0FullDensity.dPaid

theorem dUnpaid_nonneg : 0 ≤ dUnpaid := sub_nonneg.mpr D0FullDensity.dPaid_le

/-- The max-branch debit is retained: the endpoint remainder is no longer owed. -/
theorem dUnpaid_eq_min : dUnpaid =
    min (D0-SigmaRemaining.d0Paid) D0FullDensity.densityUnpaid := by
  rw [D0FullDensity.densityUnpaid_eq]
  unfold dUnpaid D0FullDensity.dPaid
  rcases le_total SigmaRemaining.d0Paid D0FullDensity.fullMass with h|h
  · rw [max_eq_right h,min_eq_right (by linarith)]
  · rw [max_eq_left h,min_eq_left (by linarith)]

theorem original_dUnpaid_balance : CorrectionD0Joint.dUnpaid =
    (D0FullDensity.dPaid-D0FullDensity.finiteD)+dUnpaid := by
  unfold CorrectionD0Joint.dUnpaid dUnpaid
  ring

/-- Exact remaining profile obligation; this definition is NOT a paid estimate. -/
def profileUnpaid : ℝ := numeratorUnpaid/(1-D0)+
  numerator*dUnpaid/((1-D0)*(1-D0FullDensity.dPaid))

theorem profileUnpaid_nonneg : 0 ≤ profileUnpaid := by
  have hD := sub_pos.mpr D0_lt_one
  have hd := sub_pos.mpr D0FullDensity.dPaid_lt_one
  exact add_nonneg (div_nonneg numeratorUnpaid_nonneg hD.le)
    (div_nonneg (mul_nonneg numerator_pos.le dUnpaid_nonneg) (mul_pos hD hd).le)

theorem actual_profile_balance : aProfile (nineProfile NineFeedbackStrength.originalH)=
    profile+profileUnpaid := by
  have hD := (sub_pos.mpr D0_lt_one).ne'
  have hd := (sub_pos.mpr D0FullDensity.dPaid_lt_one).ne'
  rw [aProfile_eq]
  unfold profile profileUnpaid numeratorUnpaid dUnpaid
  field_simp
  ring

/-- Only the true numerator/D0 residual and the original intrinsic E residual remain. -/
def remaining : ℝ := log 2*profileUnpaid+CorrectionD0Joint.intrinsicEUnpaid

theorem remaining_nonneg : 0 ≤ remaining :=
  add_nonneg (mul_nonneg (log_nonneg (by norm_num : (1:ℝ)≤2)) profileUnpaid_nonneg)
    CorrectionD0Joint.intrinsicEUnpaid_nonneg

theorem actual_terminal_balance : firstFeedback NineFeedbackStrength.originalH 3 3=
    terminal+remaining := by
  have hp := actual_profile_balance
  unfold terminal remaining CorrectionD0Joint.intrinsicEUnpaid
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  rw [hp]
  ring

/-- The original allUnpaid account is rebased, not enlarged or double-consumed. -/
theorem original_unpaid_balance : CorrectionD0Joint.allUnpaid =
    (terminal-CorrectionD0Joint.terminal)+remaining := by
  have ho := CorrectionD0Joint.actual_terminal_balance
  have hn := actual_terminal_balance
  linarith only [ho,hn]

/-- Exact original hf4 gap, not the stronger sufficient test H8 ≤ terminal. -/
theorem original_hf4_iff_remaining :
    (NineFeedbackStrength.originalH 8 ≤ firstFeedback NineFeedbackStrength.originalH 3 3) ↔
    NineFeedbackStrength.originalH 8-terminal ≤ remaining := by
  rw [actual_terminal_balance]
  exact (sub_le_iff_le_add').symm

end Hf4Den
