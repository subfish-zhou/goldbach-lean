import MathlibNt.Wu2008DoubleSieve.FourPositiveCompleteCoefficient

namespace Wu2008DoubleSieve.FourPositiveExactEnvelope
open Real FourPositiveRationalLower FourRoughClosedMass SharpLogRecurrence

noncomputable def exactTen : ℝ := (526171398671103464214455980266004229213696/59597934275976722095385338646284286266866075 : ℝ)
noncomputable def exactEleven : ℝ := (2361109236472751976071696771291076256403126272/50608518910766431617032151129056091745532164275 : ℝ)
noncomputable def exactGain : ℝ := (306667525261229222966304870769896077448437085479456768/690903400879751552354761947609632310966573718576993725 : ℝ)
noncomputable def exactUpper : ℝ := (9182572113011365096691072830959466934987736690208049813631603412893410510955623359824137891190151300043092120948010334185123504245192038829521283952976519918900097070820432152155107405727811614746983977165016379105950783700572110581229511/1656340224457205001908219700657499944864404091430399906592282325660713528949405296951736487180624541966491423286469106735091173498476729468157003110118550390030342416060201251333723069386576247357462120558989223047712018019607160000000000 : ℝ)

theorem ten_exact : rationalTen = exactTen := by
  norm_num [rationalTen,rationalTail,lowerLog,alpha,beta,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,exactTen]

theorem eleven_exact : rationalEleven = exactEleven := by
  norm_num [rationalEleven,rationalTail,rationalCross,lowerLog,alpha,beta,lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda,exactEleven]

theorem weighted_exact : weightedRational = exactGain := by
  rw [weightedRational,ten_exact,eleven_exact]
  norm_num [exactTen,exactEleven,exactGain]

theorem exact_positive_lower : 0 < exactTen ∧ exactTen ≤ I10 ∧
    0 < exactEleven ∧ exactEleven ≤ I11 := by
  rw [← ten_exact,← eleven_exact]
  exact literal_actual_lower

theorem exact_gain_positive : 0 < exactGain := by
  rw [← weighted_exact]
  exact weighted_positive

theorem exact_weighted_lower : exactGain ≤ 8*I10+8*I11 := by
  rw [← weighted_exact]
  exact actual_weighted_lower

theorem rational_upper_eq : FourPositiveCompleteCoefficient.rationalUpper = exactUpper := by
  have h := FourPositiveCompleteCoefficient.envelope_identity
  rw [JCubicExactEnvelope.rational_upper_eq,weighted_exact] at h
  have he : exactUpper+exactGain = JCubicExactEnvelope.exactUpper := by
    norm_num [exactUpper,exactGain,JCubicExactEnvelope.exactUpper]
  linarith

theorem exact_envelope_improvement : exactUpper+exactGain = JCubicExactEnvelope.exactUpper := by
  norm_num [exactUpper,exactGain,JCubicExactEnvelope.exactUpper]

theorem strict_envelope_improvement : exactUpper < JCubicExactEnvelope.exactUpper := by
  have h := exact_envelope_improvement
  have hp := exact_gain_positive
  linarith

theorem actual_exact_upper : TruncatedElevenClassicalCountLower.classicalCoefficient ≤ exactUpper := by
  rw [← rational_upper_eq]
  exact FourPositiveCompleteCoefficient.complete_rational_upper

theorem actual_exact_interval : (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient ∧
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ exactUpper :=
  ⟨RationalMovingSixth.complete_coefficient_gt_three_halves,actual_exact_upper⟩

end Wu2008DoubleSieve.FourPositiveExactEnvelope
