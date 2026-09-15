import MathlibNt.Wu2008DoubleSieve.SharpJBalance

namespace Wu2008DoubleSieve.SharpMassBalance
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpSingleBalance
open scoped Interval

noncomputable abbrev a : ℝ := truncatedSixthLowerAlpha
noncomputable abbrev b : ℝ := truncatedSixthLowerBeta
noncomputable abbrev s : ℝ := truncatedSixthLowerSigma
noncomputable def lam : ℝ := 1/2-2*a
noncomputable def m : ℝ := lam-b
noncomputable def s0 : ℝ := (1/2-2*b)/a
noncomputable def fifthDensity : ℝ := lowerLog (s0-1)/(a*s0)

 theorem four_weighted_lt_21_twentieths :
    8*FourRoughClosedMass.I10+8*FourRoughClosedMass.I11 < 21/20 := by
  have h10 := ClassicalLogFourBounds.I10_log_upper
  have h11 := ClassicalLogFourBounds.I11_log_upper
  obtain ⟨hl0,_,hu0,_⟩ := ClassicalLogFourBounds.log_caps
  have hl := log_upper (t := b/a) (by norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have hu := log_upper (t := s/b)
    (by norm_num [a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma])
  have hel : ClassicalLogFourBounds.tailLog = log (b/a) := by
    rw [log_div (by norm_num [b,truncatedSixthLowerBeta]) (by norm_num [a,truncatedSixthLowerAlpha])]
    rfl
  have heu : ClassicalLogFourBounds.crossLog = log (s/b) := by
    rw [log_div (by norm_num [s,truncatedSixthLowerSigma,truncatedSixthLowerAlpha])
      (by norm_num [b,truncatedSixthLowerBeta])]
    unfold ClassicalLogFourBounds.crossLog
    congr 1
    congr 1
    norm_num [FourRoughClosedMass.lam,FourRoughClosedMass.alpha,
      truncatedSixthLowerLambda,s,truncatedSixthLowerSigma,truncatedSixthLowerAlpha]
  rw [hel] at hl0 h10 h11
  rw [heu] at hu0 h11
  have h3 := pow_le_pow_left₀ hl0 hl 3
  have h4 := pow_le_pow_left₀ hl0 hl 4
  have hprod := mul_le_mul hu h3 (pow_nonneg hl0 _)
    (by norm_num [upperLog,s,b,truncatedSixthLowerSigma,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] : 0 ≤ upperLog (s/b))
  norm_num [ClassicalLogFourBounds.densityCap,FourRoughClosedMass.alpha,
    a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma,upperLog] at h10 h11 h3 h4 hprod
  nlinarith

 theorem fifth_density_lower {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    fifthDensity/(x*y) ≤ fifthPairRegular 0 (x,y) := by
  have ha := truncatedSixthLower_parameters.1
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hs0 : 0 < s0 := by norm_num [s0,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hs2 : 2 ≤ s0 := by norm_num [s0,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hsu : s0 ≤ truncatedSixthLowerS 0 x y := by
    apply (div_le_div_iff_of_pos_right ha).2
    dsimp [truncatedSixthLowerC]
    linarith [hxy.trans hy]
  have hz : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
    linarith [hxy.trans hy]
  have hlow := (log_lower (t := s0-1) (by linarith)).trans (lower_ge_log hs2)
  have htr := lower_ratio_transport hs0 hsu
  have hmul := mul_le_mul_of_nonneg_left hlow
    (div_nonneg (hs0.le.trans hsu) hs0.le)
  have hh := div_le_div_of_nonneg_right (hmul.trans htr) (mul_pos (mul_pos hx0 hy0) hz).le
  rw [ClassicalPositiveBounds.fifth_regular_eq hx hxy hy]
  have hz' : 1-x*2-y*2 ≠ 0 := by linarith
  convert hh using 1 <;> first | rfl | (simp only [fifthDensity,truncatedSixthLowerS,truncatedSixthLowerC,sub_zero]; field_simp [hz.ne',hz'])

 theorem fifth_log_lower :
    2*fifthDensity*(log b-log a)^2 ≤ fifthPairFlin := by
  have hp := truncatedSixthLower_parameters
  have hc : Continuous (fun v : ℝ × ℝ => fifthPairRegular 0 (v.1,v.2)) :=
    fifthPair_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun y : ℝ => ∫ x in a..y, fifthPairRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => fifthPairRegular 0 (x,y))
    · exact hc.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hi0 : IntervalIntegrable (fun y : ℝ => fifthDensity*(log y-log a)/y) volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hn (y : ℝ) (hy : y ∈ uIcc a b) : y ≠ 0 := by
      rw [uIcc_of_le hp.2.1.le] at hy; exact (hp.1.trans_le hy.1).ne'
    exact (continuousOn_const.mul ((continuousOn_id.log hn).sub continuousOn_const)).div continuousOn_id hn
  have hpoint (y : ℝ) (hy : y ∈ Icc a b) :
      fifthDensity*(log y-log a)/y ≤ ∫ x in a..y, fifthPairRegular 0 (x,y) := by
    have hy0 := hp.1.trans_le hy.1
    have hil : IntervalIntegrable (fun x : ℝ => (fifthDensity/y)*(1/x)) volume a y := by
      apply ContinuousOn.intervalIntegrable
      exact continuousOn_const.mul (continuousOn_const.div continuousOn_id (fun x hx => by
        rw [uIcc_of_le hy.1] at hx; exact (hp.1.trans_le hx.1).ne'))
    have hi := intervalIntegral.integral_mono_on hy.1 hil
      ((hc.comp (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y)
      (fun x hx => by convert fifth_density_lower hx.1 hx.2 hy.2 using 1 <;> first | rfl | ring)
    rw [intervalIntegral.integral_const_mul,integral_reciprocal hp.1 hy.1] at hi
    convert hi using 1 <;> first | rfl | ring
  have hi := intervalIntegral.integral_mono_on hp.2.1.le hi0 (hinner.intervalIntegrable a b) hpoint
  have hd (y : ℝ) (hy : y ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ => fifthDensity*(log y-log a)^2/2)
        (fifthDensity*(log y-log a)/y) y := by
    rw [uIcc_of_le hp.2.1.le] at hy
    have h := ((((hasDerivAt_log (hp.1.trans_le hy.1).ne').sub_const (log a)).pow 2).const_mul fifthDensity).div_const 2
    convert h using 1 <;> first | rfl | (simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi0] at hi
  have hf : fifthPairFlin = 4*∫ y in a..b, ∫ x in a..y, fifthPairRegular 0 (x,y) := by
    unfold fifthPairFlin fifthPairFdelta
    congr 1
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hp.2.1.le] at hy
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hy.1] at hx
    simpa [truncatedSixthLowerC] using (ClassicalPositiveBounds.fifth_regular_eq hx.1 hx.2 hy.2).symm
  rw [hf]
  norm_num at hi
  linarith

 theorem fifth_gt_three_halves : (3/2 : ℝ) < fifthPairFlin := by
  have h := fifth_log_lower
  have he : log b-log a=log (b/a) :=
    (log_div (by norm_num [b,truncatedSixthLowerBeta]) (by norm_num [a,truncatedSixthLowerAlpha])).symm
  rw [he] at h
  have hl := log_lower (t := b/a) (by norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have hl0 : 0 ≤ lowerLog (b/a) := by norm_num [lowerLog,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hsq := pow_le_pow_left₀ hl0 hl 2
  norm_num [fifthDensity,s0,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,lowerLog] at h hsq
  nlinarith

/-- The tangent to the reciprocal square is a global rational inequality. -/
theorem reciprocal_square_tangent {z : ℝ} (hz : 0 < z) : 64*(3/4-2*z) ≤ 1/z^2 := by
  apply (le_div_iff₀ (pow_pos hz 2)).2
  have h := mul_nonneg (sq_nonneg (4*z-1)) (show 0 ≤ 8*z+1 by linarith)
  nlinarith

noncomputable def polynomialKernel (x y : ℝ) : ℝ :=
  128*(lam-x-y)*(2*x+2*y-1/4)/(x*y)

 theorem sixth_polynomial_lower {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b m) :
    polynomialKernel x y ≤ truncatedSixthZeroDeltaRegular 0 (x,y) := by
  have hp := truncatedSixthLower_parameters
  have hms : m ≤ s := by norm_num [m,lam,a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]
  have hr : truncatedSixthLowerRegion 0 x y := by
    refine ⟨hx.1,hx.2,hy.1,hy.2.trans hms,?_⟩
    dsimp [m,lam] at hy
    dsimp [truncatedSixthLowerC]
    linarith [hx.2,hy.2]
  have hb := truncatedSixthLower_region_bounds (by norm_num : (0 : ℝ) ≤ 0) hr
  have hz : 0 < 1/2-x-y := by
    have hh := hb.2.2.1
    dsimp [truncatedSixthLowerC] at hh
    linarith [hp.1]
  have hu : 2 ≤ truncatedSixthLowerS 0 x y := hb.2.2.2.1
  have hlog := ClassicalLogBounds.log_tangent_lower (a := (1 : ℝ))
    (b := truncatedSixthLowerS 0 x y-1) (by norm_num) (by linarith)
  have hl := lower_ge_log hu
  have hdiv := div_le_div_of_nonneg_right
    (show 2*(truncatedSixthLowerS 0 x y-2)/truncatedSixthLowerS 0 x y ≤
      wuLowerCoefficient (truncatedSixthLowerS 0 x y) by
      norm_num only [log_one,sub_zero] at hlog
      have he : 2*(truncatedSixthLowerS 0 x y-2)/truncatedSixthLowerS 0 x y =
        2*(truncatedSixthLowerS 0 x y-1-1)/(1+(truncatedSixthLowerS 0 x y-1)) := by ring
      rw [he]; exact hlog.trans hl)
    (mul_pos (mul_pos hb.1 hb.2.1) hz).le
  have hd : 0 ≤ lam-x-y := by dsimp [m,lam] at hy ⊢; linarith [hx.2,hy.2]
  have ht := mul_le_mul_of_nonneg_left (reciprocal_square_tangent hz)
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd) (mul_pos hb.1 hb.2.1).le)
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx ⟨hy.1,hy.2.trans hms⟩,if_pos hr]
  simp only [truncatedSixthLowerC, sub_zero]
  change _ ≤ wuLowerCoefficient (truncatedSixthLowerS 0 x y)/(x*y*(1/2-x-y))
  calc
    polynomialKernel x y = (2*(lam-x-y)/(x*y))*(64*(3/4-2*(1/2-x-y))) := by
      dsimp [polynomialKernel]; ring
    _ ≤ (2*(lam-x-y)/(x*y))*(1/(1/2-x-y)^2) := ht
    _ = (2*(truncatedSixthLowerS 0 x y-2)/truncatedSixthLowerS 0 x y)/(x*y*(1/2-x-y)) := by
      have hz' : 1-x*2-y*2 ≠ 0 := by linarith
      simp only [truncatedSixthLowerS,truncatedSixthLowerC,lam,sub_zero]
      field_simp [hp.1.ne',hb.1.ne',hb.2.1.ne',hz.ne',hz']; ring
    _ ≤ _ := hdiv

end Wu2008DoubleSieve.SharpMassBalance
