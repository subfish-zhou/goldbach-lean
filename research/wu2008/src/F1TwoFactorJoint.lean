import F1ActualSecondCollected

namespace F1TwoFactor
open Real Wu2008DoubleSieve SharpLogRecurrence FirstCRationalPayment
open F1JointFTC F1ActualSecondFTC F1SecondLogRecovery
noncomputable section

def commonA : ℝ := residueA+partC+partF
def commonAC : ℝ := residueA+residueC+partC+partF
def commonB : ℝ := residueB+coeffC+coeffF/21
def baseCoefficient : ℝ := partB+coeffB

def jointMass : ℝ :=
  (1+commonB)*(log 2+log (3/2))+log (1127/600)+
  commonA*log (3884129/3606400)+commonAC*log (4508/2927)-
  commonB*log (2400/2381)+residueD*log (4508/3981)+
  baseCoefficient*log (2254/1727)+
  oneMinus*log crossOneMinus-onePlus*log crossOnePlus+
  twoMinus*log crossTwoMinus-twoPlus*log crossTwoPlus+
  rationalEndpointPart+F1JointFTC.rationalPart+rationalPartTwo+secondPayment+EJoint.payment

theorem jointMass_exact : jointMass = signedMainLogs+F1ActualSecondFTC.cPayment+EJoint.payment := by
  have h1 : log refOne=log ((3884129:ℝ)/3606400)+log (4508/2927) := by
    rw [← log_mul (by norm_num : (3884129:ℝ)/3606400 ≠ 0)
      (by norm_num : (4508:ℝ)/2927 ≠ 0)]
    norm_num [refOne]
  have h2 : log refTwo=log (2:ℝ)+log (3/2)-log (2400/2381) := by
    rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ)/2 ≠ 0),
      ← log_div (by norm_num : (2:ℝ)*(3/2) ≠ 0) (by norm_num : (2400:ℝ)/2381 ≠ 0)]
    norm_num [refTwo]
  unfold F1ActualSecondFTC.cPayment
  rw [collectedOne_exact,collectedTwo_exact]
  unfold jointMass signedMainLogs collectedOne collectedTwo commonA commonAC commonB baseCoefficient
  rw [h1,h2]
  norm_num only [partA,coeffA]
  ring

theorem jointMass_le_actual : 8*jointMass ≤ Wu08TerminalAlignment.firstMain := by
  have hc := F1ActualSecondFTC.cPayment_le_actual
  have he := EJoint.payment_le
  rw [jointMass_exact,FirstActualRecovery.actual_first_recoveries,← finiteMainPayment_exact]
  unfold logRecovery
  linarith only [hc,he]

theorem previous_mass_le : F1JointFTC.jointMass ≤ jointMass := by
  rw [F1JointFTC.jointMass_exact,jointMass_exact]
  linarith only [F1ActualSecondFTC.cPayment_ge_previous]

theorem common_signs : 0 ≤ commonA ∧ commonAC ≤ 0 ∧ commonB ≤ 0 ∧
    1+commonB ≤ 0 ∧ 0 ≤ baseCoefficient := by
  norm_num [commonA,commonAC,commonB,baseCoefficient,residueA,residueB,residueC,
    partC,partF,partB,coeffC,coeffF,coeffB]

end
end F1TwoFactor
