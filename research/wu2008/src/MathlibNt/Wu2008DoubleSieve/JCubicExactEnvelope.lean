import MathlibNt.Wu2008DoubleSieve.JCubicCompleteCoefficient

namespace Wu2008DoubleSieve.JCubicExactEnvelope
open Real SharpLogRecurrence SharpJBalance

noncomputable def exactGain : ℝ := (23444583031287192070422357573833715451819699533135366687775060934675757730955613582762899814616474647652856/41617068692843258469326931849048908071588907098521705850619932301224380682694265097774107817893785505876375 : ℝ)
noncomputable def exactUpper : ℝ := (1559151652486044775360416394124564700090612289862599445082832283999403903660081498072644970575936939066580239258990061490100764354643634288034483171384661552139339034314112341699770513104146625348554451837/260389933265598626032786779388516010490733265522196171146587268514611141567820866366632199731349958044928462341180006652439643989228249707916645386126116564414727577096921855820699794163252055720000000000 : ℝ)

theorem weighted_gain_exact : JCubicRationalLower.weightedRational-
    FixedCoefficientJLowerEnclosure.weightedRational = exactGain := by
  rw [JCubicRationalLower.weighted_exact]
  norm_num [exactGain,FixedCoefficientJLowerEnclosure.weightedRational,
    FixedCoefficientJLowerEnclosure.seventhRational,
    FixedCoefficientJLowerEnclosure.eighthRational,FixedCoefficientJLowerEnclosure.ninthRational,
    lowerLog,a,b,s,SeventhEighth.alpha,SeventhEighth.sigma,ninthProfileK2]

theorem rational_upper_eq : JCubicCompleteCoefficient.rationalUpper = exactUpper := by
  rw [JCubicCompleteCoefficient.envelope_identity,CombinedCoefficientEnclosure.rational_upper_eq]
  have h := weighted_gain_exact
  have he : CombinedCoefficientEnclosure.exactUpper-exactGain = exactUpper := by
    norm_num [CombinedCoefficientEnclosure.exactUpper,exactGain,exactUpper]
  linarith

theorem gain_positive : 0 < exactGain := by norm_num [exactGain]

theorem exact_envelope_improvement : exactUpper+exactGain = CombinedCoefficientEnclosure.exactUpper := by
  norm_num [exactUpper,exactGain,CombinedCoefficientEnclosure.exactUpper]

theorem actual_exact_upper :
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ exactUpper := by
  rw [← rational_upper_eq]
  exact JCubicCompleteCoefficient.complete_rational_upper

/-- This compares only the envelope, not the original coefficient, to the benchmark. -/
theorem envelope_above_benchmark : (899/250 : ℝ) < exactUpper := by
  norm_num [exactUpper]

theorem actual_exact_interval :
    (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient ∧
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ exactUpper :=
  ⟨RationalMovingSixth.complete_coefficient_gt_three_halves,actual_exact_upper⟩

end Wu2008DoubleSieve.JCubicExactEnvelope
