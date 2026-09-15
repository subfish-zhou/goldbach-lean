import SigmaCorrectionSameProfile
import D0FullRemainders
noncomputable section
namespace CorrectionD0Joint
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback

def base : ℝ := max SigmaCorrectionFTC.finiteProfile SigmaCorrectionFTC.paidCorrectedProfile

theorem base_le_inner : base ≤ SigmaInnerProfile.d0Lower NineFeedbackStrength.originalH :=
  max_le SigmaCorrectionFTC.finiteProfile_le_inner
    (SigmaCorrectionFTC.paidCorrectedProfile_le.trans SigmaSignedCells.correctedProfile_le_inner)

theorem old_le_base : SigmaSignedCells.profileLower ≤ base :=
  SigmaCorrectionFTC.old_profile_le_finite.trans (le_max_left _ _)

theorem base_pos : 0 < base := SigmaSignedCells.profileLower_pos.trans_le old_le_base

def numerator : ℝ := base*(1-SigmaRemaining.d0Paid)

theorem numerator_le : numerator ≤ SigmaInnerProfile.numerator NineFeedbackStrength.originalH :=
  (le_div_iff₀ (sub_pos.mpr SigmaRemaining.d0Paid_lt_one)).mp base_le_inner

def profile : ℝ := numerator/(1-D0FullDensity.finiteD)

theorem profile_le_actual : profile ≤ aProfile (nineProfile NineFeedbackStrength.originalH) := by
  have hden := sub_pos.mpr D0FullDensity.finiteD_lt_one
  calc
    profile ≤ SigmaInnerProfile.numerator NineFeedbackStrength.originalH/(1-D0FullDensity.finiteD) :=
      div_le_div_of_nonneg_right numerator_le hden.le
    _ ≤ SigmaInnerProfile.actualLower NineFeedbackStrength.originalH :=
      div_le_div_of_nonneg_left SigmaInnerProfile.original_numerator_pos.le
        (sub_pos.mpr D0_lt_one) (by linarith only [D0FullDensity.finiteD_le_D0])
    _ ≤ _ := SigmaInnerProfile.actualLower_le_profile CoupledIntegralRecovery.originalH_nonneg

theorem base_le_profile : base ≤ profile := by
  apply (le_div_iff₀ (sub_pos.mpr D0FullDensity.finiteD_lt_one)).mpr
  exact mul_le_mul_of_nonneg_left
    (by have h : SigmaRemaining.d0Paid ≤ D0FullDensity.finiteD := le_max_left _ _
        linarith only [h]) base_pos.le

theorem profile_pos : 0 < profile := base_pos.trans_le base_le_profile

theorem d0_profile_le : D0FullDensity.finiteProfile ≤ profile := by
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right old_le_base (sub_pos.mpr SigmaRemaining.d0Paid_lt_one).le)
    (sub_pos.mpr D0FullDensity.finiteD_lt_one).le

def terminal : ℝ := RemainingHf.splitLower 2*profile+
  TerminalESigned.massPaid NineFeedbackStrength.originalH

theorem terminal_le_actual : terminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have ha := mul_le_mul_of_nonneg_left profile_le_actual (log_nonneg (by norm_num : (1:ℝ)≤2))
  have hl := mul_le_mul_of_nonneg_right (RemainingHf.splitLower_le (by norm_num : (1:ℝ)≤2)) profile_pos.le
  have he := TerminalESigned.massPaid_le CoupledIntegralRecovery.originalH_nonneg
  have hm := TerminalECells.mass_le CoupledIntegralRecovery.originalH_nonneg
  unfold terminal
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [ha,hl,he,hm]

theorem old_terminal_le : D0FullDensity.finiteTerminal ≤ terminal := by
  exact add_le_add (mul_le_mul_of_nonneg_left d0_profile_le SignedSigmaETerminal.logPayment_nonneg) le_rfl
end CorrectionD0Joint
