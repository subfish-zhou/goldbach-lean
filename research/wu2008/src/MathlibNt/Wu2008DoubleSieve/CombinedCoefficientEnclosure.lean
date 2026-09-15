import MathlibNt.Wu2008DoubleSieve.RetainedSixthCoefficient
import MathlibNt.Wu2008DoubleSieve.GVariableStrength

namespace Wu2008DoubleSieve.CombinedCoefficientEnclosure
open Real ClassicalAnalyticLeaves SharpLogRecurrence FixedCoefficientUpperEnclosure

noncomputable def rationalUpper : ℝ :=
  RetainedSixthCoefficient.rationalUpper-GVariableCoefficient.rationalGain

/-- Reassemble the original terms; do not subtract independently proved K bounds. -/
theorem complete_rational_upper :
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper := by
  have hb := base_upper
  have hf := RetainedSixthCoefficient.actual_fifth_upper
  have hs := RefinedRetainedFTC.actual_sixth_upper
  have hg := GVariableCoefficient.G_pair_rational_lower
  have hj := FixedCoefficientJLowerEnclosure.weighted_J_lower
  have hi := FourRoughClosedMass.integrals_nonneg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient rationalUpper
    RetainedSixthCoefficient.rationalUpper
  linarith

theorem literal_complete_upper :
    24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
    8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))+fifthPairFlin+
    truncatedSixthLowerF6lin+47/481250-
    SingleUpperClassicalLimit.Glin (1/3)-SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma-
    8*J9-16*SeventhEighth.J7-8*SeventhEighth.J8-
    8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11 ≤ rationalUpper := complete_rational_upper

theorem improvement_gt_three : rationalUpper+3 < FixedCoefficientHLowerEnclosure.rationalUpper := by
  have hd := RetainedSixthCoefficient.upper_improvement
  have hg := GVariableStrength.rational_gain_gt_two
  unfold rationalUpper
  linarith

theorem upper_lt_eight : rationalUpper < (8 : ℝ) := by
  have hi := improvement_gt_three
  have hu := FixedCoefficientHLowerEnclosure.rationalUpper_lt_eleven
  linarith

theorem actual_interval : (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient ∧
    TruncatedElevenClassicalCountLower.classicalCoefficient < 8 :=
  ⟨RationalMovingSixth.complete_coefficient_gt_three_halves,complete_rational_upper.trans_lt upper_lt_eight⟩

noncomputable def exactUpper : ℝ := (3973947573415217148848685332748013058069127523372021034062148814537781555565338718731974223351953398334496888953756714738728703259639550889992449145564360083593502182010663847319551505500207823251/606607903095979024831681854362129818689693746368336420838256194433298803902013232940849262767292138985612419467855825374880616517167120807492745696809063945276556539013054707592439641560000000000 : ℝ)

theorem rational_upper_eq : rationalUpper = exactUpper := by
  norm_num [rationalUpper, exactUpper, RetainedSixthCoefficient.rationalUpper,
    RetainedSixthCoefficient.rationalFifth, RefinedRetainedFTC.rationalSixth,
    GVariableCoefficient.rationalGain,GVariableIntegral.affinePayment,GVariableQuadratic.quadraticPayment,
    FixedCoefficientHLowerEnclosure.rationalH,FixedCoefficientHLowerEnclosure.ratio,
    FixedCoefficientHLowerEnclosure.c,baseBound,densityConstant,lowerLog,upperLog,a,b,s,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma,
    FixedCoefficientJLowerEnclosure.weightedRational,FixedCoefficientJLowerEnclosure.seventhRational,
    FixedCoefficientJLowerEnclosure.eighthRational,FixedCoefficientJLowerEnclosure.ninthRational,
    SharpJBalance.a,SharpJBalance.b,SharpJBalance.s,SeventhEighth.alpha,SeventhEighth.sigma,ninthProfileK2]

/-- This locates the upper envelope only; it does not locate K above the benchmark. -/
theorem upper_above_benchmark : (899/250 : ℝ) < rationalUpper := by
  rw [rational_upper_eq]
  norm_num [exactUpper]

#print axioms complete_rational_upper
#print axioms actual_interval
#print axioms rational_upper_eq
end Wu2008DoubleSieve.CombinedCoefficientEnclosure
