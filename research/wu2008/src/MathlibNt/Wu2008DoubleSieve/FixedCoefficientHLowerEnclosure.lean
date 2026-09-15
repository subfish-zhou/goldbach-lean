import MathlibNt.Wu2008DoubleSieve.FixedCoefficientJLowerEnclosure

namespace Wu2008DoubleSieve.FixedCoefficientHLowerEnclosure
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientScalarEnclosure FixedCoefficientUpperEnclosure
open scoped Interval

 theorem upper_four_lower : (34832/30375 : ℝ) ≤ wuUpperCoefficient 4 := by
  have h := upper_global_lower (u := 4) (by norm_num)
  have hl := log_lower (t := 3/2) (by norm_num)
  rw [log_div (by norm_num) (by norm_num)] at hl
  norm_num [lowerLog,lowerPrimitive] at h hl
  linarith

 theorem upper_five_lower : (340/243 : ℝ) ≤ wuUpperCoefficient 5 := by
  have h := upper_global_lower (u := 5) (by norm_num)
  have he4 : log (4 : ℝ) = 2*log 2 := by
    have hh := log_pow (2 : ℝ) 2
    norm_num at hh
    exact hh
  norm_num [lowerPrimitive,he4] at h
  linarith [log_two_bounds.1]

noncomputable def c (j : ℝ) : ℝ := 1/2-j*a

 theorem segment_lower {j C l r : ℝ} (hj : 2 ≤ j) (hC : C ≤ wuUpperCoefficient j)
    (hl : a ≤ l) (hr : r ≤ c j) (hr3 : r ≤ 1/3) (hlr : l ≤ r) :
    C*(reciprocalPrimitive r-reciprocalPrimitive l) ≤
      ∫ t in l..r, ClassicalSingleBounds.g t := by
  have ha := truncatedSixthLower_parameters.1
  have hl0 := ha.trans_le hl
  have hi : IntervalIntegrable (fun t : ℝ => C/(t*(1/2-t))) volume l r := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      (fun t ht => by
        rw [uIcc_of_le hlr] at ht
        exact mul_ne_zero (hl0.trans_le ht.1).ne' (by linarith [ht.2]))
  have hm := intervalIntegral.integral_mono_on hlr hi
    (ClassicalSingleBounds.g_integrable hl hr3 hlr) (fun t ht => by
      have ht0 := hl0.trans_le ht.1
      have hd : 0 < 1/2-t := by linarith [ht.2]
      have hju : j ≤ (1/2-t)/a := (le_div_iff₀ ha).2 (by dsimp [c] at hr; linarith [ht.2])
      exact div_le_div_of_nonneg_right (hC.trans (upper_mono hj hju)) (mul_pos ht0 hd).le)
  have hd (t : ℝ) (ht : t ∈ uIcc l r) :
      HasDerivAt (fun t => C*reciprocalPrimitive t) (C/(t*(1/2-t))) t := by
    rw [uIcc_of_le hlr] at ht
    have ht0 := hl0.trans_le ht.1
    have ht1 : 1/2-t ≠ 0 := by linarith [ht.2]
    have ht2 : 1-t*2 ≠ 0 := by linarith [ht.2]
    have hh := (((hasDerivAt_log ht0.ne').sub
      (((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).log ht1)).const_mul 2).const_mul C
    convert hh using 1 <;> first | rfl | (dsimp; field_simp [ht2]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi] at hm
  linarith

noncomputable def Hbound : ℝ :=
  8*((340/243)*(reciprocalPrimitive (c 5)-reciprocalPrimitive a)+
    (34832/30375)*(reciprocalPrimitive (c 4)-reciprocalPrimitive (c 5))+
    (reciprocalPrimitive s-reciprocalPrimitive (c 4)))+
    4*(reciprocalPrimitive (1/3)-reciprocalPrimitive s)

 theorem G_pair_H_lower : Hbound ≤
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s := by
  have h5 : a ≤ c 5 := by norm_num [c,a,truncatedSixthLowerAlpha]
  have h54 : c 5 ≤ c 4 := by norm_num [c,a,truncatedSixthLowerAlpha]
  have h4s : c 4 ≤ s := by norm_num [c,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hs3 : s ≤ 1/3 := truncatedSixthLower_parameters.2.2.2.1.le
  have hu3 : (1 : ℝ) ≤ wuUpperCoefficient 3 := upper_ge_one (by norm_num)
  have hseg5 := segment_lower (by norm_num : (2 : ℝ) ≤ 5) upper_five_lower le_rfl le_rfl
    (h54.trans (h4s.trans hs3)) h5
  have hseg4 := segment_lower (by norm_num : (2 : ℝ) ≤ 4) upper_four_lower h5 le_rfl
    (h4s.trans hs3) h54
  have hseg3 := segment_lower (by norm_num : (2 : ℝ) ≤ 3) hu3 (h5.trans h54)
    (le_rfl : s ≤ c 3) hs3 h4s
  have hi5 := ClassicalSingleBounds.g_integrable le_rfl (h54.trans (h4s.trans hs3)) h5
  have hi4 := ClassicalSingleBounds.g_integrable h5 (h4s.trans hs3) h54
  have hi3 := ClassicalSingleBounds.g_integrable (h5.trans h54) hs3 h4s
  have hiH := ClassicalSingleBounds.g_integrable (h5.trans (h54.trans h4s)) le_rfl hs3
  have he1 := intervalIntegral.integral_add_adjacent_intervals hi5 hi4
  have he2 := intervalIntegral.integral_add_adjacent_intervals (hi5.trans hi4) hi3
  have he3 := intervalIntegral.integral_add_adjacent_intervals ((hi5.trans hi4).trans hi3) hiH
  have heH := ClassicalSingleBounds.high_integral_eq
  have hlogH : reciprocalPrimitive (1/3)-reciprocalPrimitive s = 2*log (6*a/s) := by
    have he := primitive_crossRatio (r := 1/3) (by norm_num) (by norm_num)
    have hes := primitive_crossRatio (r := s)
      (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
      (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
    have hdiv := log_div (x := crossRatio (1/3)) (y := crossRatio s)
      (by norm_num [crossRatio,a,truncatedSixthLowerAlpha])
      (by norm_num [crossRatio,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
    have hid : crossRatio (1/3)/crossRatio s = 6*a/s := by
      norm_num [crossRatio,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
    rw [hid] at hdiv
    linarith
  rw [← hlogH] at heH
  have hg1 : SingleUpperClassicalLimit.Glin (1/3) = 4*∫ t in a..(1/3 : ℝ), ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,
      ClassicalSingleBounds.g,ClassicalSingleBounds.a,a]
  have hg2 : SingleUpperClassicalLimit.Glin s = 4*∫ t in a..s, ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,
      ClassicalSingleBounds.g,ClassicalSingleBounds.a,a]
  rw [hg1,hg2]
  unfold Hbound
  linarith

noncomputable def ratio (l r : ℝ) : ℝ := r*(1/2-l)/(l*(1/2-r))

 theorem primitive_lower {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1/2) :
    2*lowerLog (ratio l r) ≤ reciprocalPrimitive r-reciprocalPrimitive l := by
  have hr0 := hl.trans_le hlr
  have hlh : 0 < 1/2-l := by linarith
  have hrh : 0 < 1/2-r := by linarith
  have hq : 1 ≤ ratio l r := by
    unfold ratio
    apply (le_div_iff₀ (mul_pos hl hrh)).2
    nlinarith
  have h := log_lower hq
  rw [ratio,log_div (mul_ne_zero hr0.ne' hlh.ne') (mul_ne_zero hl.ne' hrh.ne'),
    log_mul hr0.ne' hlh.ne',log_mul hl.ne' hrh.ne'] at h
  -- Parent repair: normalize the same ratio in the goal and the hypothesis.
  unfold reciprocalPrimitive ratio
  linarith

noncomputable def rationalH : ℝ :=
  16*(340/243)*lowerLog (ratio a (c 5))+
  16*(34832/30375)*lowerLog (ratio (c 5) (c 4))+
  16*lowerLog (ratio (c 4) s)+8*lowerLog (ratio s (1/3))

 theorem rationalH_lower : rationalH ≤ Hbound := by
  have h1 := primitive_lower (l := a) (r := c 5)
    (by norm_num [a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha]) (by norm_num [c,a,truncatedSixthLowerAlpha])
  have h2 := primitive_lower (l := c 5) (r := c 4)
    (by norm_num [c,a,truncatedSixthLowerAlpha])
    (by norm_num [c,a,truncatedSixthLowerAlpha]) (by norm_num [c,a,truncatedSixthLowerAlpha])
  have h3 := primitive_lower (l := c 4) (r := s)
    (by norm_num [c,a,truncatedSixthLowerAlpha])
    (by norm_num [c,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
    (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h4 := primitive_lower (l := s) (r := 1/3)
    (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
    truncatedSixthLower_parameters.2.2.2.1.le (by norm_num)
  unfold rationalH Hbound
  linarith

noncomputable def rationalUpper : ℝ := baseBound+FixedCoefficientLogMassEnclosure.rationalPositive+
  47/481250-rationalH-FixedCoefficientJLowerEnclosure.weightedRational

 theorem complete_rational_upper : TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper := by
  have hb := base_upper
  have hf := FixedCoefficientLogMassEnclosure.fifth_log_upper
  have hs := FixedCoefficientLogMassEnclosure.sixth_log_upper
  have hp := FixedCoefficientLogMassEnclosure.positive_rational_upper
  have hg := rationalH_lower.trans G_pair_H_lower
  have hj := FixedCoefficientJLowerEnclosure.weighted_J_lower
  have h4 := FourRoughClosedMass.integrals_nonneg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient rationalUpper
  linarith

 theorem rationalUpper_lt_eleven : rationalUpper < (11 : ℝ) := by
  norm_num [rationalUpper,baseBound,FixedCoefficientLogMassEnclosure.rationalPositive,densityConstant,
    rationalH,ratio,c,lowerLog,upperLog,a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma,
    FixedCoefficientJLowerEnclosure.weightedRational,FixedCoefficientJLowerEnclosure.seventhRational,
    FixedCoefficientJLowerEnclosure.eighthRational,FixedCoefficientJLowerEnclosure.ninthRational,
    SharpJBalance.a,SharpJBalance.b,SharpJBalance.s,SeventhEighth.alpha,SeventhEighth.sigma,ninthProfileK2]

 theorem rationalUpper_above_benchmark : (899/250 : ℝ) < rationalUpper := by
  norm_num [rationalUpper,baseBound,FixedCoefficientLogMassEnclosure.rationalPositive,densityConstant,
    rationalH,ratio,c,lowerLog,upperLog,a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma,
    FixedCoefficientJLowerEnclosure.weightedRational,FixedCoefficientJLowerEnclosure.seventhRational,
    FixedCoefficientJLowerEnclosure.eighthRational,FixedCoefficientJLowerEnclosure.ninthRational,
    SharpJBalance.a,SharpJBalance.b,SharpJBalance.s,SeventhEighth.alpha,SeventhEighth.sigma,ninthProfileK2]

 theorem actual_interval : (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient ∧
    TruncatedElevenClassicalCountLower.classicalCoefficient < 11 :=
  ⟨RationalMovingSixth.complete_coefficient_gt_three_halves,
    complete_rational_upper.trans_lt rationalUpper_lt_eleven⟩

end Wu2008DoubleSieve.FixedCoefficientHLowerEnclosure
