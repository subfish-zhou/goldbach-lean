import D0FullCollected

noncomputable section
namespace D0FullDensity
open Real TerminalE TerminalESigned NodeExtension FirstFeedbackIntegrals ActualNineFeedback

theorem affinePaid_le (A B C : ℝ) (hA : 0≤A) (ha : 0<A*3+B) :
    RemainingHf.signed C ((A*5+B)/(A*3+B)) ≤ C*(log (A*5+B)-log (A*3+B)) := by
  have hb := affine_ratio ha hA (by norm_num : (3:ℝ)≤5)
  have h := RemainingHf.signed_le C hb.2
  rw [log_div hb.1.ne' ha.ne'] at h
  exact h

/-- Every common affine logarithm is collected before its one signed payment. -/
def fullPaid : ℝ := rationalFull 5-rationalFull 3+
  RemainingHf.signed coeffV (5/3)+RemainingHf.signed coeffMinusOne 2+
  RemainingHf.signed coeffPlusThree (4/3)+RemainingHf.signed coeffTriple (8/5)+
  RemainingHf.signed coeffEleven (8/7)+
  RemainingHf.signed (minusCoeff (-3/2)-minusCoeff (1/2)) (leftMinus 5/leftMinus 3)+
  RemainingHf.signed (plusCoeff (-3/2)-plusCoeff (1/2)) (leftPlus 5/leftPlus 3)+
  RemainingHf.signed (minusCoeff (8/3)-zeroMinus) (rightMinus 5/rightMinus 3)+
  RemainingHf.signed (plusCoeff (8/3)-zeroPlus) (rightPlus 5/rightPlus 3)

theorem fullPaid_le : fullPaid≤fullMass := by
  have h0 := affinePaid_le 1 0 coeffV (by norm_num) (by norm_num)
  have h1 := affinePaid_le 1 (-1) coeffMinusOne (by norm_num) (by norm_num)
  have h2 := affinePaid_le 1 3 coeffPlusThree (by norm_num) (by norm_num)
  have h3 := affinePaid_le 3 1 coeffTriple (by norm_num) (by norm_num)
  have h4 := affinePaid_le 1 11 coeffEleven (by norm_num) (by norm_num)
  have h5 := affinePaid_le (9-2*radical) (-5+2*radical) (minusCoeff (-3/2)-minusCoeff (1/2))
    (by linarith only [radical_lt_four]) (by nlinarith only [radical_lt_four])
  have h6 := affinePaid_le (9+2*radical) (-5-2*radical) (plusCoeff (-3/2)-plusCoeff (1/2))
    (by linarith only [radical_pos]) (by nlinarith only [radical_pos])
  have h7 := affinePaid_le (4-radical) (20-3*radical) (minusCoeff (8/3)-zeroMinus)
    (by linarith only [radical_lt_four]) (by nlinarith only [radical_lt_four])
  have h8 := affinePaid_le (4+radical) (20+3*radical) (plusCoeff (8/3)-zeroPlus)
    (by linarith only [radical_pos]) (by nlinarith only [radical_pos])
  norm_num only [mul_one,one_mul,add_zero] at h0 h1 h2 h3 h4
  rw [fullMass_collected]
  unfold fullPaid affineLogs leftMinus leftPlus rightMinus rightPlus
  ring_nf at h5 h6 h7 h8 ⊢
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8]

theorem fullPaid_le_D0 : fullPaid≤D0 := fullPaid_le.trans fullMass_le_D0

def finiteD : ℝ := max SigmaRemaining.d0Paid fullPaid

theorem finiteD_le_D0 : finiteD≤D0 := max_le SigmaRemaining.d0Paid_le fullPaid_le_D0

theorem finiteD_lt_one : finiteD<1 := finiteD_le_D0.trans_lt D0_lt_one

def finiteProfile : ℝ := profileAt finiteD

theorem finiteProfile_le : finiteProfile≤aProfile (nineProfile NineFeedbackStrength.originalH) :=
  profileAt_le finiteD_le_D0

theorem finiteProfile_pos : 0<finiteProfile := profileAt_pos finiteD_le_D0

theorem finiteProfile_ge_old : SigmaSignedCells.profileLower≤finiteProfile :=
  old_profile_le finiteD_le_D0 (le_max_left _ _)

def finiteTerminal : ℝ := terminalAt finiteD

theorem finiteTerminal_le_actual : finiteTerminal≤firstFeedback NineFeedbackStrength.originalH 3 3 :=
  terminalAt_le_actual finiteD_le_D0

theorem finiteTerminal_ge_old : SignedSigmaETerminal.lower≤finiteTerminal := by
  unfold SignedSigmaETerminal.lower finiteTerminal terminalAt
  exact add_le_add (mul_le_mul_of_nonneg_left finiteProfile_ge_old
    SignedSigmaETerminal.logPayment_nonneg) le_rfl

end D0FullDensity
