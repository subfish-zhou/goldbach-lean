import CorrectionD0Joint

noncomputable section
namespace CorrectionD0Joint
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback

/-- The same numerator as the accepted parent, before its positive D0 denominator. -/
def sigmaUnpaid : ℝ := SigmaInnerProfile.numerator NineFeedbackStrength.originalH-numerator

theorem sigmaUnpaid_nonneg : 0 ≤ sigmaUnpaid := sub_nonneg.mpr numerator_le

def dUnpaid : ℝ := D0-D0FullDensity.finiteD

theorem dUnpaid_nonneg : 0≤dUnpaid := sub_nonneg.mpr D0FullDensity.finiteD_le_D0

/-- The max branch costs real denominator mass; neither remainder is paid twice. -/
theorem dUnpaid_balance : dUnpaid=
    D0FullDensity.endpointUnpaid+D0FullDensity.densityUnpaid-
      (D0FullDensity.finiteD-D0FullDensity.fullPaid) := by
  unfold dUnpaid
  rw [D0FullDensity.original_D0_balance]
  ring

theorem dUnpaid_eq_min : dUnpaid=min (D0-SigmaRemaining.d0Paid)
    (D0FullDensity.endpointUnpaid+D0FullDensity.densityUnpaid) := by
  rw [show D0FullDensity.endpointUnpaid+D0FullDensity.densityUnpaid=
    D0-D0FullDensity.fullPaid by linarith only [D0FullDensity.original_D0_balance]]
  unfold dUnpaid D0FullDensity.finiteD
  rcases le_total SigmaRemaining.d0Paid D0FullDensity.fullPaid with h|h
  · rw [max_eq_right h,min_eq_right (by linarith)]
  · rw [max_eq_left h,min_eq_left (by linarith)]

theorem numerator_pos : 0<numerator :=
  mul_pos base_pos (sub_pos.mpr SigmaRemaining.d0Paid_lt_one)

/-- Exact same-numerator payment of the two distinct unpaid directions. -/
def profileUnpaid : ℝ := sigmaUnpaid/(1-D0)+
  numerator*dUnpaid/((1-D0)*(1-D0FullDensity.finiteD))

theorem profileUnpaid_nonneg : 0≤profileUnpaid := by
  have hD := sub_pos.mpr D0_lt_one
  have hd := sub_pos.mpr D0FullDensity.finiteD_lt_one
  unfold profileUnpaid
  exact add_nonneg (div_nonneg sigmaUnpaid_nonneg hD.le)
    (div_nonneg (mul_nonneg numerator_pos.le dUnpaid_nonneg) (mul_pos hD hd).le)

theorem actualLower_balance : SigmaInnerProfile.actualLower NineFeedbackStrength.originalH=
    profile+profileUnpaid := by
  have hD := (sub_pos.mpr D0_lt_one).ne'
  have hd := (sub_pos.mpr D0FullDensity.finiteD_lt_one).ne'
  unfold SigmaInnerProfile.actualLower profile profileUnpaid sigmaUnpaid dUnpaid
  field_simp
  ring

/-- Original unsimplified logarithmic mass, after paying the same full D0. -/
def retainedTerminal : ℝ := log 2*SigmaInnerProfile.actualLower NineFeedbackStrength.originalH+
  TerminalECells.mass NineFeedbackStrength.originalH

theorem retainedTerminal_le_actual : retainedTerminal≤firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have ha := mul_le_mul_of_nonneg_left
    (SigmaInnerProfile.actualLower_le_profile CoupledIntegralRecovery.originalH_nonneg)
    (log_nonneg (by norm_num : (1:ℝ)≤2))
  have he := TerminalECells.mass_le CoupledIntegralRecovery.originalH_nonneg
  unfold retainedTerminal
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [ha,he]

def logUnpaid : ℝ := (log 2-RemainingHf.splitLower 2)*profile

theorem logUnpaid_nonneg : 0≤logUnpaid :=
  mul_nonneg (sub_nonneg.mpr (RemainingHf.splitLower_le (by norm_num : (1:ℝ)≤2))) profile_pos.le

def terminalUnpaid : ℝ := log 2*profileUnpaid+logUnpaid+TerminalESigned.eUnpaid

theorem terminalUnpaid_nonneg : 0≤terminalUnpaid :=
  add_nonneg (add_nonneg
    (mul_nonneg (log_nonneg (by norm_num : (1:ℝ)≤2)) profileUnpaid_nonneg)
    logUnpaid_nonneg) TerminalESigned.eUnpaid_nonneg

theorem retainedTerminal_balance : retainedTerminal=terminal+terminalUnpaid := by
  unfold retainedTerminal
  rw [actualLower_balance]
  unfold terminal terminalUnpaid logUnpaid TerminalESigned.eUnpaid
  ring

/-- This is an unconditional stronger bound, not a new finite approximation. -/
theorem terminal_with_unpaid_le_actual : terminal+terminalUnpaid≤
    firstFeedback NineFeedbackStrength.originalH 3 3 := by
  rw [← retainedTerminal_balance]
  exact retainedTerminal_le_actual

end CorrectionD0Joint
