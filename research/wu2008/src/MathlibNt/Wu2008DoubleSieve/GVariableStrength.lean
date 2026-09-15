import MathlibNt.Wu2008DoubleSieve.GVariableCoefficient

namespace Wu2008DoubleSieve.GVariableStrength
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientScalarEnclosure FixedCoefficientUpperEnclosure FixedCoefficientHLowerEnclosure
open GVariableRecurrence GVariableIntegral GVariableQuadratic GVariableCoefficient

/-- The original low-domain arguments remain in [3,6]; the affine bounds are global. -/
theorem original_low_argument_range {t : ℝ} (ht : t ∈ Icc a s) :
    3 ≤ (1/2-t)/a ∧ (1/2-t)/a ≤ 6 := by
  have ha := truncatedSixthLower_parameters.1
  constructor
  · apply (le_div_iff₀ ha).2
    have hs : s=1/2-3*a := rfl
    rw [hs] at ht
    linarith [ht.2]
  · apply (div_le_iff₀ ha).2
    have hn : 1/2-a ≤ 6*a := by norm_num [a,truncatedSixthLowerAlpha]
    linarith [ht.1]

/-- Fixed exact rational arithmetic, without numerical quadrature or sampling. -/
theorem rational_gain_gt_two : (2 : ℝ) < rationalGain := by
  norm_num [rationalGain,affinePayment,quadraticPayment,c,lowerLog,upperLog,
    a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]

theorem variable_upper_lt_nine : variableUpper < (9 : ℝ) := by
  have h1 := FixedCoefficientHLowerEnclosure.rationalUpper_lt_eleven
  have h2 := rational_gain_gt_two
  unfold variableUpper
  linarith

/-- This only locates the proved upper envelope, not the original coefficient. -/
theorem variable_upper_above_benchmark : (899/250 : ℝ) < variableUpper := by
  norm_num [variableUpper,FixedCoefficientHLowerEnclosure.rationalUpper,
    rationalGain,affinePayment,quadraticPayment,baseBound,
    FixedCoefficientLogMassEnclosure.rationalPositive,densityConstant,
    rationalH,ratio,c,lowerLog,upperLog,a,b,s,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma,
    FixedCoefficientJLowerEnclosure.weightedRational,
    FixedCoefficientJLowerEnclosure.seventhRational,
    FixedCoefficientJLowerEnclosure.eighthRational,
    FixedCoefficientJLowerEnclosure.ninthRational,
    SharpJBalance.a,SharpJBalance.b,SharpJBalance.s,
    SeventhEighth.alpha,SeventhEighth.sigma,ninthProfileK2]

theorem actual_interval : (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient ∧
    TruncatedElevenClassicalCountLower.classicalCoefficient < 9 :=
  ⟨RationalMovingSixth.complete_coefficient_gt_three_halves,
    complete_variable_upper.trans_lt variable_upper_lt_nine⟩

theorem exact_balance_improvement :
    variableUpper+2 < FixedCoefficientHLowerEnclosure.rationalUpper := by
  have h := rational_gain_gt_two
  unfold variableUpper
  linarith

#print axioms original_low_argument_range
#print axioms rational_gain_gt_two
#print axioms variable_upper_above_benchmark
#print axioms actual_interval
#print axioms exact_balance_improvement
end Wu2008DoubleSieve.GVariableStrength
