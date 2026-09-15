import TailWholeEndpoints

noncomputable section
open Real F1JointFTC F1ActualSecondFTC F1BFullFTC FreshLogBasis
namespace TailWholeCommonLog

def tailC0 : ℝ := TailFiniteFTC.AB11.c0_1+TailFiniteFTC.AB12.c0_1+TailFiniteFTC.BA11.c0_1+TailFiniteFTC.BA12.c0_1+TailFiniteFTC.BA21.c0_1+TailFiniteFTC.BA22.c0_1

def tailC1 : ℝ := TailFiniteFTC.AB21.c1_1+TailFiniteFTC.AB22.c1_1+TailFiniteFTC.BA21.c1_1+TailFiniteFTC.BA22.c1_1

def tailC2 : ℝ := TailFiniteFTC.AB11.c2_1+TailFiniteFTC.AB12.c2_1+TailFiniteFTC.BA11.c2_1+TailFiniteFTC.BA12.c2_1

def tailC3 : ℝ := TailFiniteFTC.AB21.c3_1+TailFiniteFTC.AB22.c3_1+TailFiniteFTC.BA21.c3_1+TailFiniteFTC.BA22.c3_1

def tailC4 : ℝ := TailFiniteFTC.AB11.c4_1+TailFiniteFTC.AB21.c4_1+TailFiniteFTC.BA11.c4_1+TailFiniteFTC.BA21.c4_1

def tailC5 : ℝ := TailFiniteFTC.AB11.c5_1+TailFiniteFTC.AB21.c5_1+TailFiniteFTC.BA11.c5_1+TailFiniteFTC.BA21.c5_1

def tailC6 : ℝ := TailFiniteFTC.AB12.c6_1+TailFiniteFTC.AB22.c6_1+TailFiniteFTC.BA12.c6_1+TailFiniteFTC.BA22.c6_1

def tailF0 : ℝ := TailFiniteFTC.AB11.f0+TailFiniteFTC.AB12.f0+TailFiniteFTC.BA11.f0+TailFiniteFTC.BA12.f0

def tailG0 : ℝ := TailFiniteFTC.AB11.g0+TailFiniteFTC.AB12.g0+TailFiniteFTC.BA11.g0+TailFiniteFTC.BA12.g0

def tailF1 : ℝ := TailFiniteFTC.AB21.f1+TailFiniteFTC.AB22.f1+TailFiniteFTC.BA21.f1+TailFiniteFTC.BA22.f1

def tailG1 : ℝ := TailFiniteFTC.AB21.g1+TailFiniteFTC.AB22.g1+TailFiniteFTC.BA21.g1+TailFiniteFTC.BA22.g1

def tailF2 : ℝ := TailFiniteFTC.AB11.f2+TailFiniteFTC.AB21.f2+TailFiniteFTC.BA11.f2+TailFiniteFTC.BA21.f2

def tailG2 : ℝ := TailFiniteFTC.AB11.g2+TailFiniteFTC.AB21.g2+TailFiniteFTC.BA11.g2+TailFiniteFTC.BA21.g2

def tailF3 : ℝ := TailFiniteFTC.AB12.f3+TailFiniteFTC.AB22.f3+TailFiniteFTC.BA12.f3+TailFiniteFTC.BA22.f3

def tailG3 : ℝ := TailFiniteFTC.AB12.g3+TailFiniteFTC.AB22.g3+TailFiniteFTC.BA12.g3+TailFiniteFTC.BA22.g3

def deltaA : ℝ := tailC2+tailF0

def deltaB : ℝ := tailC3+tailF1/21

def deltaC : ℝ := tailC5+tailF2/21

def deltaD : ℝ := tailC6+tailF3

def coeffA : ℝ := WholeCommonLog.coeffA+(deltaA)

def coeffAC : ℝ := WholeCommonLog.coeffAC+(deltaA+deltaC)

def coeffB : ℝ := WholeCommonLog.coeffB+(deltaB)

def coeffD : ℝ := WholeCommonLog.coeffD+(deltaD)

def coeffS : ℝ := WholeCommonLog.coeffS+(tailC4)

def coeffTwo : ℝ := WholeCommonLog.coeffTwo+(deltaB+tailC0+tailC1)

def coeffThreeHalf : ℝ := WholeCommonLog.coeffThreeHalf+(deltaB+tailC1)

def poleZero : ℝ := WholeCommonLog.poleZero+(tailC0)

def poleOne : ℝ := WholeCommonLog.poleOne+(tailC1)

def coeffAM : ℝ := WholeCommonLog.coeffAM+(aMinus tailF0 tailG0)

def coeffAP : ℝ := WholeCommonLog.coeffAP+(-(aPlus tailF0 tailG0))

def coeffTM : ℝ := WholeCommonLog.coeffTM+(tMinus tailF1 tailG1)

def coeffTP : ℝ := WholeCommonLog.coeffTP+(-(tPlus tailF1 tailG1))

def coeffBM : ℝ := WholeCommonLog.coeffBM+(bMinus tailF2 tailG2)

def coeffBP : ℝ := WholeCommonLog.coeffBP+(-(bPlus tailF2 tailG2))

def coeffDM : ℝ := WholeCommonLog.coeffDM+(dMinus tailF3 tailG3)

def coeffDP : ℝ := WholeCommonLog.coeffDP+(-(dPlus tailF3 tailG3))

def rational : ℝ := WholeCommonLog.rational+TailWholeEndpoints.AB11.rational+TailWholeEndpoints.AB12.rational+TailWholeEndpoints.AB21.rational+TailWholeEndpoints.AB22.rational+TailWholeEndpoints.BA11.rational+TailWholeEndpoints.BA12.rational+TailWholeEndpoints.BA21.rational+TailWholeEndpoints.BA22.rational

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

theorem collected_exact : WholeCommonLog.collected+ActualTailFinite.mass=collected := by
  unfold ActualTailFinite.mass
  rw [TailWholeEndpoints.AB11.collected_exact,TailWholeEndpoints.AB12.collected_exact,TailWholeEndpoints.AB21.collected_exact,TailWholeEndpoints.AB22.collected_exact,TailWholeEndpoints.BA11.collected_exact,TailWholeEndpoints.BA12.collected_exact,TailWholeEndpoints.BA21.collected_exact,TailWholeEndpoints.BA22.collected_exact]
  unfold TailWholeEndpoints.AB11.collected TailWholeEndpoints.AB12.collected TailWholeEndpoints.AB21.collected TailWholeEndpoints.AB22.collected TailWholeEndpoints.BA11.collected TailWholeEndpoints.BA12.collected TailWholeEndpoints.BA21.collected TailWholeEndpoints.BA22.collected
  rw [WholeCommonLog.normalize_A,WholeCommonLog.normalize_T,WholeCommonLog.normalize_zero,WholeCommonLog.normalize_one]
  unfold WholeCommonLog.collected collected rational coeffDP coeffDM coeffBP coeffBM coeffTP coeffTM coeffAP coeffAM poleOne poleZero coeffThreeHalf coeffTwo coeffS coeffD coeffB coeffAC coeffA deltaD deltaC deltaB deltaA tailG3 tailF3 tailG2 tailF2 tailG1 tailF1 tailG0 tailF0 tailC6 tailC5 tailC4 tailC3 tailC2 tailC1 tailC0 bRefOne bRefTwo aMinus aPlus tMinus tPlus bMinus bPlus dMinus dPlus
  ring

theorem firstMain_exact : Wu08TerminalAlignment.firstMain =
    8*(collected+TailEndpointPayment.tailRemainder+FreshCommonLog.eLoss) := by
  rw [WholeCommonLog.firstMain_exact,←collected_exact,←ActualTailFinite.mass_exact]
  unfold TailEndpointPayment.tailRemainder
  ring

theorem collected_le_actual : 8*collected ≤ Wu08TerminalAlignment.firstMain := by
  rw [firstMain_exact]
  linarith only [TailEndpointPayment.tailRemainder_nonneg,FreshCommonLog.eLoss_nonneg]

end TailWholeCommonLog
