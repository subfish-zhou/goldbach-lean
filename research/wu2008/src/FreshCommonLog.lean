import FreshLogEndpoints

noncomputable section
open Real FirstCRationalPayment F1JointFTC F1ActualSecondFTC F1BFullFTC FreshLogBasis
namespace FreshCommonLog

/-- Fresh changes at the already fixed four normalizing poles. -/
def deltaA : ℝ := F1FreshFTC.AOne.c1_1+F1FreshFTC.AOne.f+
  F1FreshFTC.BOne.c0_1+F1FreshFTC.BTwo.c0_1
def deltaB : ℝ := F1FreshFTC.ATwo.c3_1+F1FreshFTC.ATwo.f/21+
  F1FreshFTC.BOne.c1_1+F1FreshFTC.BTwo.c1_1
def deltaC : ℝ := F1FreshFTC.BOne.c3_1+F1FreshFTC.BOne.f/21
def deltaD : ℝ := F1FreshFTC.BTwo.c2_1+F1FreshFTC.BTwo.f
/-- The previously absent poles 0, 1 and -s are retained explicitly. -/
def poleZero : ℝ := F1FreshFTC.AOne.c0_1+F1FreshFTC.ATwo.c0_1
def poleOne : ℝ := F1FreshFTC.ATwo.c2_1
def poleS : ℝ := F1FreshFTC.AOne.c2_1+F1FreshFTC.ATwo.c1_1+F1FreshFTC.BOne.c2_1

def coeffA : ℝ := F1BFullFTC.commonA+deltaA
def coeffAC : ℝ := F1BFullFTC.commonAC+deltaA+deltaC
def coeffB : ℝ := F1BFullFTC.commonB+deltaB
def coeffD : ℝ := F1BFullFTC.commonD+deltaD
def coeffS : ℝ := F1TwoFactor.baseCoefficient+poleS
/-- Extract only the existing main-log factors 2 and 3; no new cut or split. -/
def coeffTwo : ℝ := 1+coeffB+poleZero+poleOne
def coeffThreeHalf : ℝ := 1+coeffB+poleOne

def coeffAM : ℝ := oneMinus+aMinus F1FreshFTC.AOne.f F1FreshFTC.AOne.g
def coeffAP : ℝ := -(onePlus+aPlus F1FreshFTC.AOne.f F1FreshFTC.AOne.g)
def coeffTM : ℝ := twoMinus+tMinus F1FreshFTC.ATwo.f F1FreshFTC.ATwo.g
def coeffTP : ℝ := -(twoPlus+tPlus F1FreshFTC.ATwo.f F1FreshFTC.ATwo.g)
def coeffBM : ℝ := bOneMinus+bMinus F1FreshFTC.BOne.f F1FreshFTC.BOne.g
def coeffBP : ℝ := -(bOnePlus+bPlus F1FreshFTC.BOne.f F1FreshFTC.BOne.g)
def coeffDM : ℝ := bTwoMinus+dMinus F1FreshFTC.BTwo.f F1FreshFTC.BTwo.g
def coeffDP : ℝ := -(bTwoPlus+dPlus F1FreshFTC.BTwo.f F1FreshFTC.BTwo.g)

def rational : ℝ := rationalEndpointPart+F1JointFTC.rationalPart+
  rationalPartTwo+rationalOne+rationalTwo+
  FreshLogEndpoints.AOne.rational+FreshLogEndpoints.ATwo.rational+
  FreshLogEndpoints.BOne.rational+FreshLogEndpoints.BTwo.rational

/-- All eight kernels collected before any sign-dependent logarithm payment. -/
def collected : ℝ :=
  coeffTwo*log 2+coeffThreeHalf*log (3/2)+log (1127/600)+
  coeffA*log (3884129/3606400)+coeffAC*log (4508/2927)-
  coeffB*log (2400/2381)+coeffD*log (4508/3981)+coeffS*log (2254/1727)+
  poleZero*log (927/800)+poleOne*log (727/600)+
  coeffAM*log crossOneMinus+coeffAP*log crossOnePlus+
  coeffTM*log crossTwoMinus+coeffTP*log crossTwoPlus+
  coeffBM*log bCrossOneMinus+coeffBP*log bCrossOnePlus+
  coeffDM*log bCrossTwoMinus+coeffDP*log bCrossTwoPlus+rational+EJoint.payment

theorem collected_exact : FreshFTCJoint.joint = collected := by
  have h1 : log refOne=log ((3884129:ℝ)/3606400)+log (4508/2927) := by
    rw [← log_mul (by norm_num : (3884129:ℝ)/3606400 ≠ 0)
      (by norm_num : (4508:ℝ)/2927 ≠ 0)]
    norm_num [refOne]
  have h2 : log refTwo=log (2:ℝ)+log (3/2)-log (2400/2381) := by
    rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ)/2 ≠ 0),
      ← log_div (by norm_num : (2:ℝ)*(3/2) ≠ 0) (by norm_num : (2400:ℝ)/2381 ≠ 0)]
    norm_num [refTwo]
  have hz : log ((927:ℝ)/400)=log 2+log (927/800) := by
    rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (927:ℝ)/800 ≠ 0)]
    norm_num
  have ho : log ((727:ℝ)/200)=log 2+log (3/2)+log (727/600) := by
    rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ)/2 ≠ 0),
      ← log_mul (by norm_num : (2:ℝ)*(3/2) ≠ 0) (by norm_num : (727:ℝ)/600 ≠ 0)]
    norm_num
  unfold FreshFTCJoint.joint FreshFTCJoint.exactMass
  rw [FreshLogEndpoints.AOne.collected_exact,FreshLogEndpoints.ATwo.collected_exact,
    FreshLogEndpoints.BOne.collected_exact,FreshLogEndpoints.BTwo.collected_exact]
  unfold F1BFullFTC.collectedJoint FreshLogEndpoints.AOne.collected
    FreshLogEndpoints.ATwo.collected FreshLogEndpoints.BOne.collected FreshLogEndpoints.BTwo.collected
  rw [h1,h2,hz,ho]
  unfold collected coeffTwo coeffThreeHalf coeffA coeffAC coeffB coeffD coeffS
    deltaA deltaB deltaC deltaD poleZero poleOne poleS coeffAM coeffAP coeffTM coeffTP
    coeffBM coeffBP coeffDM coeffDP rational bRefOne bRefTwo
  ring

theorem collected_le_actual : 8*collected ≤ Wu08TerminalAlignment.firstMain := by
  rw [← collected_exact]
  exact FreshFTCJoint.joint_le_actual
end FreshCommonLog
