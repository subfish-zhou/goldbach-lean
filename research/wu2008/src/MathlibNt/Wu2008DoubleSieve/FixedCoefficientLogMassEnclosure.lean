import MathlibNt.Wu2008DoubleSieve.FixedCoefficientUpperEnclosure

namespace Wu2008DoubleSieve.FixedCoefficientLogMassEnclosure
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure
open scoped Interval

 theorem reciprocal_integrable {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
    IntervalIntegrable (fun t : ℝ => 1/t) volume l r :=
  (continuousOn_const.div continuousOn_id (fun t ht => by
    rw [uIcc_of_le hlr] at ht
    exact (hl.trans_le ht.1).ne')).intervalIntegrable

 theorem fifth_density {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    fifthPairRegular 0 (x,y) ≤ densityConstant/(x*y) := by
  rw [ClassicalPositiveBounds.fifth_regular_eq hx hxy hy]
  apply positive_density_upper hx (hx.trans hxy)
  have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
  linarith

 theorem sixth_density {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b s) :
    truncatedSixthZeroDeltaRegular 0 (x,y) ≤ densityConstant/(x*y) := by
  have hp := truncatedSixthLower_parameters
  have ha := hp.1
  have hx0 := hp.1.trans_le hx.1
  have hy0 := (hp.1.trans hp.2.1).trans_le hy.1
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx hy]
  split_ifs with hr
  · have hb := truncatedSixthLower_region_bounds (by norm_num : (0 : ℝ) ≤ 0) hr
    norm_num only [truncatedSixthLowerC,mul_zero,sub_zero]
    apply positive_density_upper hx.1 (hp.2.1.le.trans hy.1)
    have hh := hb.2.2.1
    norm_num only [truncatedSixthLowerC,mul_zero,sub_zero] at hh
    linarith [hp.1]
  · unfold densityConstant
    positivity

noncomputable def fifthLog : ℝ := 2*densityConstant*(log b-log a)^2
noncomputable def sixthLog : ℝ := 4*densityConstant*(log b-log a)*(log s-log b)

 theorem fifth_log_upper : fifthPairFlin ≤ fifthLog := by
  have hp := truncatedSixthLower_parameters
  have ha := hp.1
  have hab := hp.2.1.le
  have hc : Continuous (fun v : ℝ × ℝ => fifthPairRegular 0 (v.1,v.2)) :=
    fifthPair_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun y : ℝ => ∫ x in a..y, fifthPairRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => fifthPairRegular 0 (x,y))
    · exact hc.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hmajor : IntervalIntegrable (fun y : ℝ => densityConstant*(log y-log a)/y) volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hlog : ContinuousOn log (uIcc a b) := continuousOn_log.mono (by
      intro y hy
      rw [uIcc_of_le hab] at hy
      exact (ha.trans_le hy.1).ne')
    exact (continuousOn_const.mul (hlog.sub continuousOn_const)).div continuousOn_id (fun y hy => by
      rw [uIcc_of_le hab] at hy
      exact (ha.trans_le hy.1).ne')
  have hm := intervalIntegral.integral_mono_on hab (hinner.intervalIntegrable a b) hmajor
    (fun y hy => by
      have hy0 := ha.trans_le hy.1
      have hir := (reciprocal_integrable ha hy.1).const_mul (densityConstant/y)
      have hpoint (x : ℝ) (hx : x ∈ Icc a y) :
          fifthPairRegular 0 (x,y) ≤ (densityConstant/y)*(1/x) := by
        convert fifth_density hx.1 hx.2 hy.2 using 1
        ring
      have hh := intervalIntegral.integral_mono_on hy.1
        ((hc.comp (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y) hir hpoint
      rw [intervalIntegral.integral_const_mul,integral_reciprocal ha hy.1] at hh
      simpa only [Function.comp_apply, div_mul_eq_mul_div] using hh)
  have hd (y : ℝ) (hy : y ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ => densityConstant*(log y-log a)^2/2)
        (densityConstant*(log y-log a)/y) y := by
    rw [uIcc_of_le hab] at hy
    have hh := (((((hasDerivAt_log (ha.trans_le hy.1).ne').sub_const (log a)).pow 2).const_mul
      densityConstant).div_const 2)
    convert hh using 1 <;> first | rfl | (dsimp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hmajor] at hm
  have he : fifthPairFlin = 4*∫ y in a..b, ∫ x in a..y, fifthPairRegular 0 (x,y) := by
    unfold fifthPairFlin fifthPairFdelta
    congr 1
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hab] at hy
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hy.1] at hx
    simpa [truncatedSixthLowerC] using (ClassicalPositiveBounds.fifth_regular_eq hx.1 hx.2 hy.2).symm
  rw [he]
  dsimp [fifthLog]
  norm_num at hm
  linarith

 theorem sixth_log_upper : truncatedSixthLowerF6lin ≤ sixthLog := by
  have hp := truncatedSixthLower_parameters
  have ha := hp.1
  have hb := hp.1.trans hp.2.1
  have hab := hp.2.1.le
  have hbs := hp.2.2.1.le
  have hc : Continuous (fun v : ℝ × ℝ => truncatedSixthZeroDeltaRegular 0 (v.1,v.2)) :=
    truncatedSixthZeroDelta_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun x : ℝ => ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral
      (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)) hc <;> fun_prop
  have hm := intervalIntegral.integral_mono_on hab (hinner.intervalIntegrable a b)
    ((reciprocal_integrable ha hab).const_mul (densityConstant*(log s-log b))) (fun x hx => by
      have hh := intervalIntegral.integral_mono_on hbs
        ((hc.comp (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable b s)
        ((reciprocal_integrable hb hbs).const_mul (densityConstant/x)) (fun y hy => by
          convert sixth_density hx hy using 1 <;> first | rfl | ring)
      rw [intervalIntegral.integral_const_mul,integral_reciprocal hb hbs] at hh
      convert hh using 1 <;> first | rfl | ring)
  rw [intervalIntegral.integral_const_mul,integral_reciprocal ha hab] at hm
  have he := truncatedSixthZeroDelta_extension_eq (by norm_num : (0 : ℝ) ≤ 0)
  change (4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) =
    truncatedSixthLowerF6lin at he
  rw [← he]
  dsimp [sixthLog]
  nlinarith only [hm]

noncomputable def rationalPositive : ℝ :=
  2*densityConstant*(upperLog (b/a))^2+
    4*densityConstant*upperLog (b/a)*upperLog (s/b)

 theorem positive_rational_upper : fifthLog+sixthLog ≤ rationalPositive := by
  have hp := truncatedSixthLower_parameters
  have ha := hp.1
  have hb := hp.1.trans hp.2.1
  have hs := hb.trans hp.2.2.1
  have h1 := log_upper (t := b/a) ((le_div_iff₀ ha).2 (by linarith [hp.2.1]))
  have h2 := log_upper (t := s/b) ((le_div_iff₀ hb).2 (by linarith [hp.2.2.1]))
  have hn1 : 0 ≤ log b-log a := sub_nonneg.mpr (log_le_log ha hp.2.1.le)
  have hn2 : 0 ≤ log s-log b := sub_nonneg.mpr (log_le_log hb hp.2.2.1.le)
  rw [log_div hb.ne' ha.ne'] at h1
  rw [log_div hs.ne' hb.ne'] at h2
  have hm1 := mul_le_mul h1 h1 hn1 (hn1.trans h1)
  have hm2 := mul_le_mul h1 h2 hn2 (hn1.trans h1)
  have hC : 0 ≤ densityConstant := by unfold densityConstant; positivity
  have hh1 := mul_le_mul_of_nonneg_left hm1 hC
  have hh2 := mul_le_mul_of_nonneg_left hm2 hC
  unfold fifthLog sixthLog rationalPositive
  nlinarith only [hh1,hh2]

noncomputable def rationalUpper : ℝ := baseBound+rationalPositive+47/481250-rationalG

 theorem complete_rational_upper : TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper := by
  have hb := base_upper
  have hf := fifth_log_upper
  have hs := sixth_log_upper
  have hp := positive_rational_upper
  have hg := rationalG_lower.trans G_pair_lower
  have h7 := SeventhEighth.J7_nonneg
  have h8 := SeventhEighth.J8_nonneg
  have h9 := J9_nonneg
  have h4 := FourRoughClosedMass.integrals_nonneg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient rationalUpper
  linarith

 theorem rationalUpper_lt_twenty_eight : rationalUpper < (28 : ℝ) := by
  norm_num [rationalUpper,baseBound,rationalPositive,densityConstant,rationalG,lowerLog,upperLog,
    crossRatio,a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]

 theorem actual_interval : (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient ∧
    TruncatedElevenClassicalCountLower.classicalCoefficient < 28 :=
  ⟨RationalMovingSixth.complete_coefficient_gt_three_halves,
    complete_rational_upper.trans_lt rationalUpper_lt_twenty_eight⟩

end Wu2008DoubleSieve.FixedCoefficientLogMassEnclosure
