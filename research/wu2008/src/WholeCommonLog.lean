import WholeCrossEndpoints

noncomputable section
open Real F1JointFTC F1ActualSecondFTC F1BFullFTC FreshLogBasis
namespace WholeCommonLog

def crossC0 : ℝ := F1CrossFTC.A1D.c0_1+F1CrossFTC.A2D.c0_1+F1CrossFTC.A1B1.c0_1+F1CrossFTC.A1B2.c0_1+F1CrossFTC.A2B1.c0_1+F1CrossFTC.A2B2.c0_1

def crossC1 : ℝ := F1CrossFTC.A2D.c1_1+F1CrossFTC.A2B1.c1_1+F1CrossFTC.A2B2.c1_1

def crossC2 : ℝ := F1CrossFTC.A1D.c2_1+F1CrossFTC.A1B1.c2_1+F1CrossFTC.A1B2.c2_1+F1CrossFTC.AB1.c2_1+F1CrossFTC.AB2.c2_1

def crossC3 : ℝ := F1CrossFTC.A2D.c3_1+F1CrossFTC.A2B1.c3_1+F1CrossFTC.A2B2.c3_1+F1CrossFTC.AB1.c3_1+F1CrossFTC.AB2.c3_1

def crossC4 : ℝ := F1CrossFTC.A1D.c4_1+F1CrossFTC.A2D.c4_1+F1CrossFTC.A1B1.c4_1+F1CrossFTC.A2B1.c4_1+F1CrossFTC.AB1.c4_1

def crossC5 : ℝ := F1CrossFTC.A1D.c5_1+F1CrossFTC.A2D.c5_1+F1CrossFTC.A1B1.c5_1+F1CrossFTC.A2B1.c5_1+F1CrossFTC.AB1.c5_1

def crossC6 : ℝ := F1CrossFTC.A1D.c6_1+F1CrossFTC.A2D.c6_1+F1CrossFTC.A1B2.c6_1+F1CrossFTC.A2B2.c6_1+F1CrossFTC.AB2.c6_1

def crossF0 : ℝ := F1CrossFTC.A1D.f0+F1CrossFTC.A1B1.f0+F1CrossFTC.A1B2.f0

def crossG0 : ℝ := F1CrossFTC.A1D.g0+F1CrossFTC.A1B1.g0+F1CrossFTC.A1B2.g0

def crossF1 : ℝ := F1CrossFTC.A2D.f1+F1CrossFTC.A2B1.f1+F1CrossFTC.A2B2.f1

def crossG1 : ℝ := F1CrossFTC.A2D.g1+F1CrossFTC.A2B1.g1+F1CrossFTC.A2B2.g1

def crossF2 : ℝ := F1CrossFTC.A1B1.f2+F1CrossFTC.A2B1.f2+F1CrossFTC.AB1.f2

def crossG2 : ℝ := F1CrossFTC.A1B1.g2+F1CrossFTC.A2B1.g2+F1CrossFTC.AB1.g2

def crossF3 : ℝ := F1CrossFTC.A1B2.f3+F1CrossFTC.A2B2.f3+F1CrossFTC.AB2.f3

def crossG3 : ℝ := F1CrossFTC.A1B2.g3+F1CrossFTC.A2B2.g3+F1CrossFTC.AB2.g3

def deltaA : ℝ := crossC2+crossF0

def deltaB : ℝ := crossC3+crossF1/21

def deltaC : ℝ := crossC5+crossF2/21

def deltaD : ℝ := crossC6+crossF3

def coeffA : ℝ := FreshCommonLog.coeffA+deltaA

def coeffAC : ℝ := FreshCommonLog.coeffAC+deltaA+deltaC

def coeffB : ℝ := FreshCommonLog.coeffB+deltaB

def coeffD : ℝ := FreshCommonLog.coeffD+deltaD

def coeffS : ℝ := FreshCommonLog.coeffS+crossC4

def coeffTwo : ℝ := FreshCommonLog.coeffTwo+deltaB+crossC0+crossC1

def coeffThreeHalf : ℝ := FreshCommonLog.coeffThreeHalf+deltaB+crossC1

def poleZero : ℝ := FreshCommonLog.poleZero+crossC0

def poleOne : ℝ := FreshCommonLog.poleOne+crossC1

def coeffAM : ℝ := FreshCommonLog.coeffAM+aMinus crossF0 crossG0

def coeffAP : ℝ := FreshCommonLog.coeffAP-aPlus crossF0 crossG0

def coeffTM : ℝ := FreshCommonLog.coeffTM+tMinus crossF1 crossG1

def coeffTP : ℝ := FreshCommonLog.coeffTP-tPlus crossF1 crossG1

def coeffBM : ℝ := FreshCommonLog.coeffBM+bMinus crossF2 crossG2

def coeffBP : ℝ := FreshCommonLog.coeffBP-bPlus crossF2 crossG2

def coeffDM : ℝ := FreshCommonLog.coeffDM+dMinus crossF3 crossG3

def coeffDP : ℝ := FreshCommonLog.coeffDP-dPlus crossF3 crossG3

def rational : ℝ := FreshCommonLog.rational+WholeCrossEndpoints.A1D.rational+WholeCrossEndpoints.A2D.rational+WholeCrossEndpoints.A1B1.rational+WholeCrossEndpoints.A1B2.rational+WholeCrossEndpoints.A2B1.rational+WholeCrossEndpoints.A2B2.rational+WholeCrossEndpoints.AB1.rational+WholeCrossEndpoints.AB2.rational

def collected : ℝ := (coeffTwo)*log (2)+
  (coeffThreeHalf)*log (3/2)+
  (1)*log (1127/600)+
  (coeffA)*log (3884129/3606400)+
  (coeffAC)*log (4508/2927)+
  (-coeffB)*log (2400/2381)+
  (coeffD)*log (4508/3981)+
  (coeffS)*log (2254/1727)+
  (poleZero)*log (927/800)+
  (poleOne)*log (727/600)+
  (coeffAM)*log (crossOneMinus)+
  (coeffAP)*log (crossOnePlus)+
  (coeffTM)*log (crossTwoMinus)+
  (coeffTP)*log (crossTwoPlus)+
  (coeffBM)*log (bCrossOneMinus)+
  (coeffBP)*log (bCrossOnePlus)+
  (coeffDM)*log (bCrossTwoMinus)+
  (coeffDP)*log (bCrossTwoPlus)+rational+EJoint.payment

theorem normalize_A : log refOne=log ((3884129:ℝ)/3606400)+log (4508/2927) := by
  rw [← log_mul (by norm_num : (3884129:ℝ)/3606400 ≠ 0) (by norm_num : (4508:ℝ)/2927 ≠ 0)]
  norm_num [refOne]
theorem normalize_T : log refTwo=log (2:ℝ)+log (3/2)-log (2400/2381) := by
  rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ)/2 ≠ 0),
    ← log_div (by norm_num : (2:ℝ)*(3/2) ≠ 0) (by norm_num : (2400:ℝ)/2381 ≠ 0)]
  norm_num [refTwo]
theorem normalize_zero : log ((927:ℝ)/400)=log 2+log (927/800) := by
  rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (927:ℝ)/800 ≠ 0)]
  norm_num
theorem normalize_one : log ((727:ℝ)/200)=log 2+log (3/2)+log (727/600) := by
  rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ)/2 ≠ 0),
    ← log_mul (by norm_num : (2:ℝ)*(3/2) ≠ 0) (by norm_num : (727:ℝ)/600 ≠ 0)]
  norm_num

theorem collected_exact : F1CrossMass.joint=collected := by
  unfold F1CrossMass.joint F1CrossMass.mass
  rw [WholeCrossEndpoints.A1D.collected_exact,WholeCrossEndpoints.A2D.collected_exact,WholeCrossEndpoints.A1B1.collected_exact,WholeCrossEndpoints.A1B2.collected_exact,WholeCrossEndpoints.A2B1.collected_exact,WholeCrossEndpoints.A2B2.collected_exact,WholeCrossEndpoints.AB1.collected_exact,WholeCrossEndpoints.AB2.collected_exact]
  unfold WholeCrossEndpoints.A1D.collected WholeCrossEndpoints.A2D.collected WholeCrossEndpoints.A1B1.collected WholeCrossEndpoints.A1B2.collected WholeCrossEndpoints.A2B1.collected WholeCrossEndpoints.A2B2.collected WholeCrossEndpoints.AB1.collected WholeCrossEndpoints.AB2.collected
  rw [normalize_A,normalize_T,normalize_zero,normalize_one]
  unfold FreshCommonLog.collected collected rational coeffDP coeffDM coeffBP coeffBM coeffTP coeffTM coeffAP coeffAM poleOne poleZero coeffThreeHalf coeffTwo coeffS coeffD coeffB coeffAC coeffA deltaD deltaC deltaB deltaA crossG3 crossF3 crossG2 crossF2 crossG1 crossF1 crossG0 crossF0 crossC6 crossC5 crossC4 crossC3 crossC2 crossC1 crossC0 bRefOne bRefTwo aMinus aPlus tMinus tPlus bMinus bPlus dMinus dPlus
  ring

theorem firstMain_exact : Wu08TerminalAlignment.firstMain =
    8*(collected+F1CrossMass.tailMass+FreshCommonLog.eLoss) := by
  rw [F1CrossMass.firstMain_exact,collected_exact]

theorem collected_le_actual : 8*collected ≤ Wu08TerminalAlignment.firstMain := by
  rw [← collected_exact]
  exact F1CrossMass.joint_le_actual
end WholeCommonLog
