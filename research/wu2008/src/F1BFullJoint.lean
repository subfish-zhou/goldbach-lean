import F1BFullCollected

noncomputable section
open Real FirstCRationalPayment F1JointFTC F1ActualSecondFTC
namespace F1BFullFTC

def commonA : ℝ := F1TwoFactor.commonA+oneA+twoA
def commonAC : ℝ := F1TwoFactor.commonAC+oneA+twoA+oneC+oneF/21
def commonB : ℝ := F1TwoFactor.commonB+oneB+twoB
def commonD : ℝ := residueD+twoC+twoF

def collectedJoint : ℝ :=
  (1+commonB)*(log 2+log (3/2))+log (1127/600)+
  commonA*log (3884129/3606400)+commonAC*log (4508/2927)-
  commonB*log (2400/2381)+commonD*log (4508/3981)+
  F1TwoFactor.baseCoefficient*log (2254/1727)+
  oneMinus*log crossOneMinus-onePlus*log crossOnePlus+
  twoMinus*log crossTwoMinus-twoPlus*log crossTwoPlus+
  bOneMinus*log bCrossOneMinus-bOnePlus*log bCrossOnePlus+
  bTwoMinus*log bCrossTwoMinus-bTwoPlus*log bCrossTwoPlus+
  rationalEndpointPart+F1JointFTC.rationalPart+rationalPartTwo+rationalOne+rationalTwo+EJoint.payment

theorem collectedJoint_exact : jointMass = collectedJoint := by
  have h1 : log refOne=log ((3884129:ℝ)/3606400)+log (4508/2927) := by
    rw [← log_mul (by norm_num : (3884129:ℝ)/3606400 ≠ 0)
      (by norm_num : (4508:ℝ)/2927 ≠ 0)]
    norm_num [refOne]
  have h2 : log refTwo=log (2:ℝ)+log (3/2)-log (2400/2381) := by
    rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ)/2 ≠ 0),
      ← log_div (by norm_num : (2:ℝ)*(3/2) ≠ 0) (by norm_num : (2400:ℝ)/2381 ≠ 0)]
    norm_num [refTwo]
  unfold jointMass exactMass
  rw [collectedOne_exact,collectedTwo_exact]
  unfold F1TwoFactor.jointMass collectedJoint collectedOne collectedTwo
  rw [h1,h2]
  unfold commonA commonAC commonB commonD bRefOne bRefTwo
  ring

theorem common_signs : 0 ≤ commonA ∧ commonAC ≤ 0 ∧ commonB ≤ 0 ∧
    1+commonB ≤ 0 ∧ commonD ≤ 0 := by
  norm_num [commonA,commonAC,commonB,commonD,F1TwoFactor.commonA,F1TwoFactor.commonAC,
    F1TwoFactor.commonB,residueA,residueB,residueC,residueD,partC,partF,coeffC,coeffF,
    oneA,twoA,oneB,twoB,oneC,oneF,twoC,twoF]

/-- Apply the already authorized once-only log payment after coefficient collection. -/
def jointLower : ℝ :=
  (1+commonB)*F1JointSplit.twoUpper+F1JointSplit.paid (1+commonB) (3/2)+
  F1JointSplit.paid 1 (1127/600)+F1JointSplit.paid commonA (3884129/3606400)+
  F1JointSplit.paid commonAC (4508/2927)+F1JointSplit.paid (-commonB) (2400/2381)+
  F1JointSplit.paid commonD (4508/3981)+F1JointSplit.paid F1TwoFactor.baseCoefficient (2254/1727)+
  F1JointSplit.paid oneMinus crossOneMinus+F1JointSplit.paid (-onePlus) crossOnePlus+
  F1JointSplit.paid twoMinus crossTwoMinus+F1JointSplit.paid (-twoPlus) crossTwoPlus+
  F1JointSplit.paid bOneMinus bCrossOneMinus+F1JointSplit.paid (-bOnePlus) bCrossOnePlus+
  F1JointSplit.paid bTwoMinus bCrossTwoMinus+F1JointSplit.paid (-bTwoPlus) bCrossTwoPlus+
  rationalEndpointPart+F1JointFTC.rationalPart+rationalPartTwo+rationalOne+rationalTwo+EJoint.payment

theorem jointLower_le_mass : jointLower ≤ jointMass := by
  obtain ⟨hxm,hxp,hym,hyp⟩ := cross_arguments
  obtain ⟨hbxm,hbxp,hbym,hbyp⟩ := b_cross_arguments
  have h0 := mul_le_mul_of_nonpos_left F1JointSplit.log_two_le common_signs.2.2.2.1
  have h1 := F1JointSplit.paid_le (1+commonB) (by norm_num : (1:ℝ)≤3/2)
  have h2 := F1JointSplit.paid_le 1 (by norm_num : (1:ℝ)≤1127/600)
  have h3 := F1JointSplit.paid_le commonA (by norm_num : (1:ℝ)≤3884129/3606400)
  have h4 := F1JointSplit.paid_le commonAC (by norm_num : (1:ℝ)≤4508/2927)
  have h5 := F1JointSplit.paid_le (-commonB) (by norm_num : (1:ℝ)≤2400/2381)
  have h6 := F1JointSplit.paid_le commonD (by norm_num : (1:ℝ)≤4508/3981)
  have h7 := F1JointSplit.paid_le F1TwoFactor.baseCoefficient (by norm_num : (1:ℝ)≤2254/1727)
  have h8 := F1JointSplit.paid_le oneMinus hxm
  have h9 := F1JointSplit.paid_le (-onePlus) hxp
  have h10 := F1JointSplit.paid_le twoMinus hym
  have h11 := F1JointSplit.paid_le (-twoPlus) hyp
  have h12 := F1JointSplit.paid_le bOneMinus hbxm
  have h13 := F1JointSplit.paid_le (-bOnePlus) hbxp
  have h14 := F1JointSplit.paid_le bTwoMinus hbym
  have h15 := F1JointSplit.paid_le (-bTwoPlus) hbyp
  rw [collectedJoint_exact]
  unfold jointLower collectedJoint
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15]

theorem jointLower_le_actual : 8*jointLower ≤ Wu08TerminalAlignment.firstMain := by
  linarith only [jointLower_le_mass,jointMass_le_actual]

end F1BFullFTC
