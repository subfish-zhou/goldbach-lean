import MathlibNt.Wu2008DoubleSieve.FixedCoefficientScalarEnclosure

namespace Wu2008DoubleSieve.FixedCoefficientUpperEnclosure
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientScalarEnclosure
open scoped Interval

noncomputable abbrev a : ℝ := truncatedSixthLowerAlpha
noncomputable abbrev b : ℝ := truncatedSixthLowerBeta
noncomputable abbrev s : ℝ := truncatedSixthLowerSigma
noncomputable def densityConstant : ℝ := 43/(150*a)

 theorem lower_after_five {t : ℝ} (ht : 5 ≤ t) :
    wuLowerCoefficient t ≤ 203/144+(311/1080)*(t-5) := by
  have h5 := lower_quartic_upper (s := 5) (by norm_num) le_rfl
  have he4 : log (4 : ℝ) = 2*log 2 := by
    have hh := log_pow (2 : ℝ) 2
    norm_num at hh
    exact hh
  have h2 := log_two_bounds.2
  norm_num [quartic, he4] at h5
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 5) ht
  have hab : 4 ≤ t-1 := by linarith
  have hi := intervalIntegral.integral_mono_on hab
    (wuUpperCoefficient_div_intervalIntegrable (by norm_num) hab)
    (intervalIntegrable_const (c := (311/1080 : ℝ)) (μ := volume)) (fun u hu =>
      (SharpSingleBalance.upper_ratio_antitone (by norm_num : (0 : ℝ) < 4) hu.1).trans
        upper_four_div)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  norm_num only [show (5 : ℝ)-1=4 by norm_num] at hr
  linarith

noncomputable def baseBound : ℝ :=
  24*(203/144+(311/1080)*(1/(2*a)-5))+8*(11/10+(1/(2*b)-4)/3)

 theorem base_upper :
    24*wuLowerCoefficient (1/(2*a))+8*wuLowerCoefficient (1/(2*b)) ≤ baseBound := by
  have h1 := lower_after_five (t := 1/(2*a)) (by norm_num [a,truncatedSixthLowerAlpha])
  have h2 := lower_affine_upper (s := 1/(2*b)) (by norm_num [b,truncatedSixthLowerBeta])
  have h3 := log_three_bounds.2
  unfold baseBound
  linarith

 theorem positive_density_upper {x y : ℝ} (hx : a ≤ x) (hy : a ≤ y)
    (hrem : 0 < 1/2-x-y) :
    wuLowerCoefficient (truncatedSixthLowerS 0 x y)/(x*y*(1/2-x-y)) ≤
      densityConstant/(x*y) := by
  have ha := truncatedSixthLower_parameters.1
  have hx0 := ha.trans_le hx
  have hy0 := ha.trans_le hy
  have hS : 0 < truncatedSixthLowerS 0 x y := by
    apply div_pos _ ha
    simpa [truncatedSixthLowerC] using hrem
  have hS5 : truncatedSixthLowerS 0 x y ≤ 5 := by
    apply (div_le_iff₀ ha).2
    dsimp [truncatedSixthLowerC]
    have hnum : (1/2 : ℝ)-2*a ≤ 5*a := by norm_num [a,truncatedSixthLowerAlpha]
    linarith
  have hl := lower_linear_upper hS hS5
  apply (div_le_iff₀ (mul_pos (mul_pos hx0 hy0) hrem)).2
  calc
    wuLowerCoefficient (truncatedSixthLowerS 0 x y) ≤ (43/150)*truncatedSixthLowerS 0 x y := hl
    _ = densityConstant/(x*y)*(x*y*(1/2-x-y)) := by
      dsimp [densityConstant,truncatedSixthLowerS,truncatedSixthLowerC]
      field_simp
      ring

 theorem fifth_regular_upper {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    fifthPairRegular 0 (x,y) ≤ densityConstant/(a*a) := by
  have ha := truncatedSixthLower_parameters.1
  have hy0 := ha.trans_le (hx.trans hxy)
  have hd : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
    linarith
  rw [ClassicalPositiveBounds.fifth_regular_eq hx hxy hy]
  have hp := positive_density_upper hx (hx.trans hxy) hd
  apply hp.trans
  apply div_le_div_of_nonneg_left (by unfold densityConstant; positivity)
    (mul_pos ha ha) (mul_le_mul hx (hx.trans hxy) ha.le (ha.trans_le hx).le)

 theorem sixth_regular_upper {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b s) :
    truncatedSixthZeroDeltaRegular 0 (x,y) ≤ densityConstant/(a*b) := by
  have ha := truncatedSixthLower_parameters.1
  have hab := truncatedSixthLower_parameters.2.1.le
  have hb := ha.trans_le hab
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx hy]
  split_ifs with hr
  · have hbounds := truncatedSixthLower_region_bounds (by norm_num : (0 : ℝ) ≤ 0) hr
    have hd : 0 < 1/2-x-y := by
      have hh := hbounds.2.2.1
      dsimp [truncatedSixthLowerC] at hh
      linarith
    have hp := positive_density_upper hx.1 (hab.trans hy.1) hd
    norm_num only [truncatedSixthLowerC, mul_zero, sub_zero]
    apply hp.trans
    apply div_le_div_of_nonneg_left (by unfold densityConstant; positivity)
      (mul_pos ha hb) (mul_le_mul hx.1 hy.1 hb.le (ha.trans_le hx.1).le)
  · unfold densityConstant
    positivity

noncomputable def fifthBound : ℝ := 2*(densityConstant/(a*a))*(b-a)^2
noncomputable def sixthBound : ℝ := 4*(densityConstant/(a*b))*(b-a)*(s-b)

 theorem fifth_upper : fifthPairFlin ≤ fifthBound := by
  have hp := truncatedSixthLower_parameters
  have hc : Continuous (fun v : ℝ × ℝ => fifthPairRegular 0 (v.1,v.2)) :=
    fifthPair_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun y : ℝ => ∫ x in a..y, fifthPairRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => fifthPairRegular 0 (x,y))
    · exact hc.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) hp.2.1.le
    (hinner.intervalIntegrable a b)
    ((by fun_prop : Continuous (fun y : ℝ => (densityConstant/(a*a))*(y-a))).intervalIntegrable a b)
    (fun y hy => by
      have hh := intervalIntegral.integral_mono_on hy.1
        ((hc.comp (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y)
        (intervalIntegrable_const (c := densityConstant/(a*a)) (μ := volume))
        (fun x hx => fifth_regular_upper hx.1 hx.2 hy.2)
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm, Function.comp_apply] using hh)
  have hd (y : ℝ) (_hy : y ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ => (densityConstant/(a*a))*(y-a)^2/2)
        ((densityConstant/(a*a))*(y-a)) y := by
    convert (((((hasDerivAt_id y).sub_const a).pow 2).const_mul
      (densityConstant/(a*a))).div_const 2) using 1 <;> first | rfl | (dsimp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous (fun y : ℝ => (densityConstant/(a*a))*(y-a))).intervalIntegrable a b)] at hm
  have he : fifthPairFlin = 4*∫ y in a..b, ∫ x in a..y, fifthPairRegular 0 (x,y) := by
    unfold fifthPairFlin fifthPairFdelta
    congr 1
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hp.2.1.le] at hy
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hy.1] at hx
    simpa [truncatedSixthLowerC] using (ClassicalPositiveBounds.fifth_regular_eq hx.1 hx.2 hy.2).symm
  rw [he]
  dsimp [fifthBound]
  norm_num at hm
  linarith

 theorem sixth_upper : truncatedSixthLowerF6lin ≤ sixthBound := by
  have hp := truncatedSixthLower_parameters
  have hc : Continuous (fun v : ℝ × ℝ => truncatedSixthZeroDeltaRegular 0 (v.1,v.2)) :=
    truncatedSixthZeroDelta_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun x : ℝ => ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral
      (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)) hc <;> fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) hp.2.1.le (hinner.intervalIntegrable a b)
    (intervalIntegrable_const (c := (s-b)*(densityConstant/(a*b))) (μ := volume)) (fun x hx => by
      have hh := intervalIntegral.integral_mono_on hp.2.2.1.le
        ((hc.comp (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable b s)
        (intervalIntegrable_const (c := densityConstant/(a*b)) (μ := volume))
        (fun y hy => sixth_regular_upper hx hy)
      simpa only [intervalIntegral.integral_const, smul_eq_mul, Function.comp_apply] using hh)
  have he := truncatedSixthZeroDelta_extension_eq (by norm_num : (0 : ℝ) ≤ 0)
  change (4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) =
    truncatedSixthLowerF6lin at he
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
  rw [← he]
  dsimp [sixthBound]
  nlinarith only [hm]

/-- A lower bound for a negatively signed original kernel. -/
 theorem g_lower {t : ℝ} (ht : t ∈ Icc a (1/3 : ℝ)) :
    1/(t*(1/2-t)) ≤ ClassicalSingleBounds.g t := by
  have ha := truncatedSixthLower_parameters.1
  have ht0 := ha.trans_le ht.1
  have hd : 0 < 1/2-t := by linarith [ht.2]
  have hu : 1 ≤ (1/2-t)/a := by
    apply (le_div_iff₀ ha).2
    have ha1 : a ≤ 1/6 := by norm_num [a,truncatedSixthLowerAlpha]
    linarith [ht.2]
  exact div_le_div_of_nonneg_right (upper_ge_one hu) (mul_pos ht0 hd).le

noncomputable def reciprocalPrimitive (t : ℝ) : ℝ := 2*(log t-log (1/2-t))

 theorem G_window_lower {r : ℝ} (hr : a ≤ r) (hr3 : r ≤ 1/3) :
    4*(reciprocalPrimitive r-reciprocalPrimitive a) ≤ SingleUpperClassicalLimit.Glin r := by
  have ha := truncatedSixthLower_parameters.1
  have hi : IntervalIntegrable (fun t : ℝ => 1/(t*(1/2-t))) volume a r := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      (fun t ht => by
        rw [uIcc_of_le hr] at ht
        exact mul_ne_zero (ha.trans_le ht.1).ne' (by linarith [ht.2]))
  have hd (t : ℝ) (ht : t ∈ uIcc a r) :
      HasDerivAt reciprocalPrimitive (1/(t*(1/2-t))) t := by
    rw [uIcc_of_le hr] at ht
    have ht0 := ha.trans_le ht.1
    have ht1 : 1/2-t ≠ 0 := by linarith [ht.2]
    have hh := ((hasDerivAt_log ht0.ne').sub
      (((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).log ht1)).const_mul 2
    have ht2 : 1-t*2 ≠ 0 := by linarith [ht.2]
    convert hh using 1 <;> first | rfl | (dsimp; field_simp [ht2]; ring)
  have hm := intervalIntegral.integral_mono_on hr hi
    (ClassicalSingleBounds.g_integrable le_rfl hr3 hr)
    (fun t ht => g_lower ⟨ht.1, ht.2.trans hr3⟩)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi] at hm
  have he : SingleUpperClassicalLimit.Glin r = 4*∫ t in a..r, ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,
      sub_zero,ClassicalSingleBounds.g,ClassicalSingleBounds.a,a]
  rw [he]
  linarith

noncomputable def Gbound : ℝ :=
  4*(reciprocalPrimitive (1/3)-reciprocalPrimitive a)+
  4*(reciprocalPrimitive s-reciprocalPrimitive a)

 theorem G_pair_lower : Gbound ≤
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s := by
  have hp := truncatedSixthLower_parameters
  have h1 := G_window_lower (r := 1/3)
    ((hp.2.1.le.trans hp.2.2.1.le).trans hp.2.2.2.1.le) le_rfl
  have h2 := G_window_lower (hp.2.1.le.trans hp.2.2.1.le) hp.2.2.2.1.le
  unfold Gbound
  linarith

noncomputable def upperEnvelope : ℝ :=
  baseBound+fifthBound+sixthBound+47/481250-Gbound-
    8*J9-16*SeventhEighth.J7-8*SeventhEighth.J8-
    8*FourRoughClosedMass.I10-8*FourRoughClosedMass.I11

/-- The literal whole signed coefficient, without missing terms or consumer hypotheses. -/
 theorem complete_coefficient_upper :
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ upperEnvelope := by
  have hb := base_upper
  have hf := fifth_upper
  have hs := sixth_upper
  have hg := G_pair_lower
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient upperEnvelope
  linarith

noncomputable def crossRatio (r : ℝ) : ℝ := r*(1/2-a)/(a*(1/2-r))

 theorem primitive_crossRatio {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) :
    reciprocalPrimitive r-reciprocalPrimitive a = 2*log (crossRatio r) := by
  have ha := truncatedSixthLower_parameters.1
  have ha1 : 0 < 1/2-a := by norm_num [a,truncatedSixthLowerAlpha]
  have hr1 : 0 < 1/2-r := by linarith
  rw [crossRatio, log_div (mul_ne_zero hr.ne' ha1.ne') (mul_ne_zero ha.ne' hr1.ne'),
    log_mul hr.ne' ha1.ne', log_mul ha.ne' hr1.ne']
  unfold reciprocalPrimitive
  ring

 theorem fixed_log_lower {q : ℝ} (hq : 4 ≤ q) :
    2*(56/81)+lowerLog (q/4) ≤ log q := by
  have hq0 : 0 < q := by linarith
  have hl := log_lower (t := q/4) (by linarith)
  have he4 : log (4 : ℝ) = 2*log 2 := by
    have hh := log_pow (2 : ℝ) 2
    norm_num at hh
    exact hh
  rw [log_div hq0.ne' (by norm_num),he4] at hl
  linarith [log_two_bounds.1]

noncomputable def rationalG : ℝ := 32*(56/81)+
  8*lowerLog (crossRatio (1/3)/4)+8*lowerLog (crossRatio s/4)

 theorem rationalG_lower : rationalG ≤ Gbound := by
  have h1 := fixed_log_lower (q := crossRatio (1/3)) (by
    norm_num [crossRatio,a,truncatedSixthLowerAlpha])
  have h2 := fixed_log_lower (q := crossRatio s) (by
    norm_num [crossRatio,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  unfold Gbound
  rw [primitive_crossRatio (by norm_num) (by norm_num),
    primitive_crossRatio (by norm_num [s,a,truncatedSixthLowerSigma,truncatedSixthLowerAlpha])
      (by norm_num [s,a,truncatedSixthLowerSigma,truncatedSixthLowerAlpha])]
  unfold rationalG
  linarith

noncomputable def rationalUpper : ℝ := baseBound+fifthBound+sixthBound+47/481250-rationalG

 theorem complete_coefficient_rational_upper :
    TruncatedElevenClassicalCountLower.classicalCoefficient ≤ rationalUpper := by
  have hk := complete_coefficient_upper
  have hg := rationalG_lower
  have h7 := SeventhEighth.J7_nonneg
  have h8 := SeventhEighth.J8_nonneg
  have h9 := J9_nonneg
  have h4 := FourRoughClosedMass.integrals_nonneg
  unfold upperEnvelope rationalUpper at *
  linarith

 theorem rationalUpper_lt_thirty_five : rationalUpper < (35 : ℝ) := by
  norm_num [rationalUpper,baseBound,fifthBound,sixthBound,densityConstant,rationalG,
    lowerLog,crossRatio,a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]

 theorem actual_interval :
    (3/2 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient ∧
    TruncatedElevenClassicalCountLower.classicalCoefficient < 35 :=
  ⟨RationalMovingSixth.complete_coefficient_gt_three_halves,
    complete_coefficient_rational_upper.trans_lt rationalUpper_lt_thirty_five⟩

 theorem rationalUpper_above_benchmark : (899/250 : ℝ) < rationalUpper := by
  norm_num [rationalUpper,baseBound,fifthBound,sixthBound,densityConstant,rationalG,
    lowerLog,crossRatio,a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]

end Wu2008DoubleSieve.FixedCoefficientUpperEnclosure
