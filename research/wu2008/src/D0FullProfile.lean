import D0FullFTC
import SignedSigmaETerminal

noncomputable section
namespace D0FullDensity
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback

/-- A same-numerator inequality, proved before any denominator replacement. -/
theorem signed_le_same_numerator : SigmaSignedCells.profileLower ≤
    SigmaInnerProfile.d0Lower NineFeedbackStrength.originalH := by
  apply SigmaSignedCells.profileLower_le_primitive.trans
  exact max_le SigmaInnerProfile.old_finiteLower_le SigmaPrimitiveCells.elementaryLower_le

def paidNumerator : ℝ := SigmaSignedCells.profileLower*(1-SigmaRemaining.d0Paid)

theorem paidNumerator_le : paidNumerator ≤ SigmaInnerProfile.numerator NineFeedbackStrength.originalH :=
  (le_div_iff₀ (sub_pos.mpr SigmaRemaining.d0Paid_lt_one)).mp signed_le_same_numerator

theorem paidNumerator_pos : 0<paidNumerator :=
  mul_pos SigmaSignedCells.profileLower_pos (sub_pos.mpr SigmaRemaining.d0Paid_lt_one)

def profileAt (d : ℝ) : ℝ := paidNumerator/(1-d)

theorem profileAt_le {d : ℝ} (hd : d ≤ D0) :
    profileAt d ≤ aProfile (nineProfile NineFeedbackStrength.originalH) := by
  have hden : 0<1-d := sub_pos.mpr (hd.trans_lt D0_lt_one)
  calc
    profileAt d ≤ SigmaInnerProfile.numerator NineFeedbackStrength.originalH/(1-d) :=
      div_le_div_of_nonneg_right paidNumerator_le hden.le
    _ ≤ SigmaInnerProfile.actualLower NineFeedbackStrength.originalH :=
      div_le_div_of_nonneg_left SigmaInnerProfile.original_numerator_pos.le
        (sub_pos.mpr D0_lt_one) (by linarith only [hd])
    _ ≤ _ := SigmaInnerProfile.actualLower_le_profile CoupledIntegralRecovery.originalH_nonneg

theorem profileAt_pos {d : ℝ} (hd : d ≤ D0) : 0<profileAt d :=
  div_pos paidNumerator_pos (sub_pos.mpr (hd.trans_lt D0_lt_one))

theorem old_profile_le {d : ℝ} (hd : d ≤ D0) (hold : SigmaRemaining.d0Paid ≤ d) :
    SigmaSignedCells.profileLower ≤ profileAt d := by
  apply (le_div_iff₀ (sub_pos.mpr (hd.trans_lt D0_lt_one))).mpr
  exact mul_le_mul_of_nonneg_left (by linarith only [hold]) SigmaSignedCells.profileLower_pos.le

/-- The old certificate is preserved, never substituted for the actual D0. -/
def dPaid : ℝ := max SigmaRemaining.d0Paid fullMass

theorem dPaid_le : dPaid ≤ D0 := max_le SigmaRemaining.d0Paid_le fullMass_le_D0

theorem dPaid_lt_one : dPaid<1 := dPaid_le.trans_lt D0_lt_one

def profileLower : ℝ := profileAt dPaid

theorem profileLower_le : profileLower ≤ aProfile (nineProfile NineFeedbackStrength.originalH) :=
  profileAt_le dPaid_le

theorem profileLower_pos : 0<profileLower := profileAt_pos dPaid_le

theorem profileLower_ge_old : SigmaSignedCells.profileLower ≤ profileLower :=
  old_profile_le dPaid_le (le_max_left _ _)

def terminalAt (d : ℝ) : ℝ := RemainingHf.splitLower 2*profileAt d+
  TerminalESigned.massPaid NineFeedbackStrength.originalH

theorem terminalAt_le_actual {d : ℝ} (hd : d≤D0) :
    terminalAt d ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have hs := mul_le_mul_of_nonneg_left (profileAt_le hd)
    (log_nonneg (by norm_num : (1:ℝ)≤2))
  have hl := mul_le_mul_of_nonneg_right (RemainingHf.splitLower_le (by norm_num : (1:ℝ)≤2))
    (profileAt_pos hd).le
  have hm := TerminalESigned.massPaid_le CoupledIntegralRecovery.originalH_nonneg
  have he := TerminalECells.mass_le CoupledIntegralRecovery.originalH_nonneg
  unfold terminalAt
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [hs,hl,hm,he]

def terminalLower : ℝ := terminalAt dPaid

theorem terminalLower_le_actual : terminalLower ≤ firstFeedback NineFeedbackStrength.originalH 3 3 :=
  terminalAt_le_actual dPaid_le

theorem terminalLower_ge_old : SignedSigmaETerminal.lower ≤ terminalLower := by
  unfold SignedSigmaETerminal.lower terminalLower terminalAt
  exact add_le_add (mul_le_mul_of_nonneg_left profileLower_ge_old
    SignedSigmaETerminal.logPayment_nonneg) le_rfl

end D0FullDensity
