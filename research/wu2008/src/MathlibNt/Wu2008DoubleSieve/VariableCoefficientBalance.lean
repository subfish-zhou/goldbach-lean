import MathlibNt.Wu2008DoubleSieve.VariableGIntegral

namespace Wu2008DoubleSieve.VariableCoefficientBalance
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence VariableGIntegral
open scoped Interval

/-- A rational payment obtained from variable-endpoint FTC, with all signs retained. -/
noncomputable def rationalG : ℝ :=
  (8/a)*((42823/151875)*upperLog (c 5/a)+(311/1080)*upperLog (c 4/c 5))+
    8*(logCoefficient*upperLog (s/c 4)+linearCoefficient*(s-c 4)-
      (s^2-(c 4)^2)/(24*a^3)+11*upperLog (4/3))+8*upperLog (6*a/s)

 theorem full_G_rational :
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s ≤ rationalG := by
  have h := full_G_upper
  rw [endpoint] at h
  have h1 := log_upper (t := c 5/a)
    (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,a,truncatedSixthLowerAlpha])
  have h2 := log_upper (t := c 4/c 5)
    (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha])
  have h3 := log_upper (t := s/c 4)
    (by norm_num [s,c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h4 := log_upper (t := (4/3 : ℝ)) (by norm_num)
  have h5 := log_upper (t := 6*a/s)
    (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  unfold rationalG
  norm_num [logCoefficient,linearCoefficient,a,truncatedSixthLowerAlpha] at h h1 h5 ⊢
  linarith

 theorem G_payment_saves_one : rationalG+1 < (179/4 : ℝ) := by
  norm_num [rationalG,logCoefficient,linearCoefficient,upperLog,a,s,c,
    SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]

noncomputable def balance : ℝ :=
  54035471/1012500+3/2+PositiveClassicalCoefficient.rectangleBound+47/481250-
    rationalG-12-21/20

/-- The new saving is paid into the original eleven-term coefficient, unconditionally. -/
 theorem complete_coefficient_gt_balance :
    balance < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := SharpSingleBalance.base_sharp_lower
  have hg := full_G_rational
  have hj := SharpJBalance.weighted_J_lt_twelve
  have h4 := SharpMassBalance.four_weighted_lt_21_twentieths
  have hp := SharpMassBalance.fifth_gt_three_halves
  have hq := PositiveClassicalCoefficient.actual_sixth_ge_rational
  change SingleUpperClassicalLimit.Glin (1/3)+
    SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma ≤ rationalG at hg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient balance
  linarith

 theorem balance_gt_five_quarters : (5/4 : ℝ) < balance := by
  norm_num [balance,rationalG,logCoefficient,linearCoefficient,upperLog,lowerLog,a,s,c,
    SharpSingleBalance.c,SharpSingleBalance.a,PositiveClassicalCoefficient.rectangleBound,
    SharpMassBalance.a,SharpMassBalance.b,SharpMassBalance.m,SharpMassBalance.lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]

 theorem complete_coefficient_gt_five_quarters :
    (5/4 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient :=
  balance_gt_five_quarters.trans complete_coefficient_gt_balance

 theorem exact_balance_improvement :
    (54035471/1012500+3/2+PositiveClassicalCoefficient.rectangleBound+47/481250-
      179/4-12-21/20)+1 < balance := by
  have h := G_payment_saves_one
  unfold balance
  linarith

/-- This lower envelope alone does not settle the engineering comparison. -/
 theorem balance_below_engineering_benchmark : balance < (899/250 : ℝ) := by
  norm_num [balance,rationalG,logCoefficient,linearCoefficient,upperLog,lowerLog,a,s,c,
    SharpSingleBalance.c,SharpSingleBalance.a,PositiveClassicalCoefficient.rectangleBound,
    SharpMassBalance.a,SharpMassBalance.b,SharpMassBalance.m,SharpMassBalance.lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]

 theorem literal_coefficient_gt_five_quarters :
    (5/4 : ℝ) <
      24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
      8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+fifthPairFlin+
      truncatedSixthLowerF6lin+47/481250-
      SingleUpperClassicalLimit.Glin (1/3)-
      SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma-8*J9-
      16*SeventhEighth.J7-8*SeventhEighth.J8-
      8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11 :=
  complete_coefficient_gt_five_quarters

end Wu2008DoubleSieve.VariableCoefficientBalance
