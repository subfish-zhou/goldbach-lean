import MathlibNt.Wu2008DoubleSieve.SixthReciprocalCount

namespace Wu2008DoubleSieve.SixthLogCubicCorrection
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope
open scoped Interval

/-- Squaring the inherited reciprocal lower bound is legal only on the original mask. -/
theorem retained_cubic_pos {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (lam-x)) :
    0 < SixthReciprocalCorrection.cubic (1/2-x-y) := by
  have hz := SixthReciprocalCorrection.retained_z_bounds hx hy
  have hb : (1/2-a-b : ℝ) < 3/8 := by
    norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hd := SixthReciprocalCorrection.correction_nonneg (hz.2.1.trans hz.2.2.le)
  have he := SixthReciprocalCorrection.correction_difference (1/2-x-y)
  linarith

theorem retained_square_lower {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (lam-x)) :
    SixthReciprocalCorrection.cubic (1/2-x-y)^2 ≤ 1/(1/2-x-y)^4 := by
  have hz := SixthReciprocalCorrection.retained_z_bounds hx hy
  have hp : 0 < 1/2-x-y := by linarith [geometry.1]
  have h := mul_self_le_mul_self (retained_cubic_pos hx hy).le
    (SixthReciprocalCorrection.cubic_lower hp)
  have he : (1/(1/2-x-y)^2)*(1/(1/2-x-y)^2) = 1/(1/2-x-y)^4 := by
    field_simp
  rw [he] at h
  simpa only [← sq] using h

noncomputable def logCubicKernel (x y : ℝ) : ℝ :=
  (2/3)*(lam-x-y)^3*SixthReciprocalCorrection.cubic (1/2-x-y)^2/(x*y)

theorem logCubicKernel_nonneg {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) : 0 ≤ logCubicKernel x y := by
  unfold logCubicKernel
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (pow_nonneg (by linarith [hy.2]) _)) (sq_nonneg _))
    (mul_pos (geometry.1.trans_le hx.1) (geometry.2.2.1.trans_le hy.1)).le

theorem logCubicKernel_terminal (x : ℝ) : logCubicKernel x (lam-x) = 0 := by
  unfold logCubicKernel
  have h : lam-x-(lam-x) = 0 := by ring
  rw [h]; simp

/-- Both lower-log terms are consumed together before comparison with the actual kernel. -/
theorem retained_joint_lower {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    polynomialKernel x y + SixthReciprocalCorrection.correctionKernel x y +
      logCubicKernel x y ≤ truncatedSixthZeroDeltaRegular 0 (x,y) := by
  have hp := truncatedSixthLower_parameters
  have hys := hy.2.trans (moving_geometry hx).2
  have hr : truncatedSixthLowerRegion 0 x y := by
    refine ⟨hx.1,hx.2,hy.1,hys,?_⟩
    dsimp [truncatedSixthLowerC]
    have hd : y ≤ 1/2-2*a-x := hy.2
    linarith
  have hb := truncatedSixthLower_region_bounds (by norm_num : (0 : ℝ) ≤ 0) hr
  have hz : 0 < 1/2-x-y := by
    have hh := hb.2.2.1
    dsimp [truncatedSixthLowerC] at hh
    linarith [hp.1]
  have hu : 2 ≤ truncatedSixthLowerS 0 x y := hb.2.2.2.1
  have hl := (log_lower (t := truncatedSixthLowerS 0 x y-1) (by linarith)).trans (lower_ge_log hu)
  have hdiv := div_le_div_of_nonneg_right hl (mul_pos (mul_pos hb.1 hb.2.1) hz).le
  have hd : 0 ≤ lam-x-y := by linarith [hy.2]
  have ht := mul_le_mul_of_nonneg_left (SixthReciprocalCorrection.cubic_lower hz)
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd) (mul_pos hb.1 hb.2.1).le)
  have hs := mul_le_mul_of_nonneg_left (retained_square_lower hx hy)
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2/3) (pow_nonneg hd 3))
      (mul_pos hb.1 hb.2.1).le)
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx ⟨hy.1,hys⟩,if_pos hr]
  simp only [truncatedSixthLowerC,sub_zero]
  change _ ≤ wuLowerCoefficient (truncatedSixthLowerS 0 x y)/(x*y*(1/2-x-y))
  calc
    polynomialKernel x y + SixthReciprocalCorrection.correctionKernel x y + logCubicKernel x y =
        (2*(lam-x-y)/(x*y))*SixthReciprocalCorrection.cubic (1/2-x-y) +
        ((2/3)*(lam-x-y)^3/(x*y))*SixthReciprocalCorrection.cubic (1/2-x-y)^2 := by
      dsimp [polynomialKernel,SixthReciprocalCorrection.correctionKernel,
        SixthReciprocalCorrection.correction,SixthReciprocalCorrection.cubic,logCubicKernel]
      ring
    _ ≤ (2*(lam-x-y)/(x*y))*(1/(1/2-x-y)^2) +
        ((2/3)*(lam-x-y)^3/(x*y))*(1/(1/2-x-y)^4) := add_le_add ht hs
    _ = lowerLog (truncatedSixthLowerS 0 x y-1)/(x*y*(1/2-x-y)) := by
      have hz' : 1-x*2-y*2 ≠ 0 := by linarith
      simp only [lowerLog,truncatedSixthLowerS,truncatedSixthLowerC,lam,sub_zero]
      field_simp [hp.1.ne',hb.1.ne',hb.2.1.ne',hz.ne',hz']; ring
    _ ≤ _ := hdiv

noncomputable def d0 (x : ℝ) : ℝ := -32+512*x-2304*x^2+4096*x^3
noncomputable def d1 (x : ℝ) : ℝ := 512-4608*x+12288*x^2
noncomputable def d2 (x : ℝ) : ℝ := -2304+12288*x
noncomputable def d3 : ℝ := 4096
noncomputable def Q0 (x : ℝ) : ℝ := (d0 x)*(d0 x)
noncomputable def Q1 (x : ℝ) : ℝ := (d0 x)*(d1 x)+(d1 x)*(d0 x)
noncomputable def Q2 (x : ℝ) : ℝ := (d0 x)*(d2 x)+(d1 x)*(d1 x)+(d2 x)*(d0 x)
noncomputable def Q3 (x : ℝ) : ℝ := (d0 x)*(d3)+(d1 x)*(d2 x)+(d2 x)*(d1 x)+(d3)*(d0 x)
noncomputable def Q4 (x : ℝ) : ℝ := (d1 x)*(d3)+(d2 x)*(d2 x)+(d3)*(d1 x)
noncomputable def Q5 (x : ℝ) : ℝ := (d2 x)*(d3)+(d3)*(d2 x)
noncomputable def Q6 (_x : ℝ) : ℝ := (d3)*(d3)
noncomputable def A0 (x : ℝ) : ℝ := (1)*(lam-x)^3*Q0 x
noncomputable def A1 (x : ℝ) : ℝ := (1)*(lam-x)^3*Q1 x+(-3)*(lam-x)^2*Q0 x
noncomputable def A2 (x : ℝ) : ℝ := (1)*(lam-x)^3*Q2 x+(-3)*(lam-x)^2*Q1 x+(3)*(lam-x)^1*Q0 x
noncomputable def A3 (x : ℝ) : ℝ := (1)*(lam-x)^3*Q3 x+(-3)*(lam-x)^2*Q2 x+(3)*(lam-x)^1*Q1 x+(-1)*(lam-x)^0*Q0 x
noncomputable def A4 (x : ℝ) : ℝ := (1)*(lam-x)^3*Q4 x+(-3)*(lam-x)^2*Q3 x+(3)*(lam-x)^1*Q2 x+(-1)*(lam-x)^0*Q1 x
noncomputable def A5 (x : ℝ) : ℝ := (1)*(lam-x)^3*Q5 x+(-3)*(lam-x)^2*Q4 x+(3)*(lam-x)^1*Q3 x+(-1)*(lam-x)^0*Q2 x
noncomputable def A6 (x : ℝ) : ℝ := (1)*(lam-x)^3*Q6 x+(-3)*(lam-x)^2*Q5 x+(3)*(lam-x)^1*Q4 x+(-1)*(lam-x)^0*Q3 x
noncomputable def A7 (x : ℝ) : ℝ := (-3)*(lam-x)^2*Q6 x+(3)*(lam-x)^1*Q5 x+(-1)*(lam-x)^0*Q4 x
noncomputable def A8 (x : ℝ) : ℝ := (3)*(lam-x)^1*Q6 x+(-1)*(lam-x)^0*Q5 x
noncomputable def A9 (x : ℝ) : ℝ := (-1)*(lam-x)^0*Q6 x

/-- Fixed degree-nine expansion, no extension of the mask inequality to y=0. -/
theorem numerator_expansion (x y : ℝ) :
    (lam-x-y)^3*SixthReciprocalCorrection.cubic (1/2-x-y)^2 = A0 x*y^0+A1 x*y^1+A2 x*y^2+A3 x*y^3+A4 x*y^4+A5 x*y^5+A6 x*y^6+A7 x*y^7+A8 x*y^8+A9 x*y^9 := by
  unfold SixthReciprocalCorrection.cubic A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 Q0 Q1 Q2 Q3 Q4 Q5 Q6 d0 d1 d2 d3
  ring

noncomputable def polynomialPart (x y : ℝ) : ℝ := A1 x*y^1/1+A2 x*y^2/2+A3 x*y^3/3+A4 x*y^4/4+A5 x*y^5/5+A6 x*y^6/6+A7 x*y^7/7+A8 x*y^8/8+A9 x*y^9/9
noncomputable def innerPrimitive (x y : ℝ) : ℝ := (2/(3*x))*(A0 x*log y+polynomialPart x y)
noncomputable def movingLogCubic (x : ℝ) : ℝ := innerPrimitive x (lam-x)-innerPrimitive x b

theorem initial_identity (x : ℝ) :
    A0 x = (lam-x)^3*SixthReciprocalCorrection.cubic (1/2-x)^2 := by
  unfold A0 Q0 d0 SixthReciprocalCorrection.cubic
  ring

/-- P here may be negative: this is a square coefficient, not a mask extension. -/
theorem moving_log_coefficient_nonneg {x : ℝ} (hx : x ∈ Icc a b) :
    0 ≤ (2/(3*x))*A0 x := by
  rw [initial_identity]
  exact mul_nonneg (div_nonneg (by norm_num) (mul_pos (by norm_num)
    (geometry.1.trans_le hx.1)).le)
    (mul_nonneg (pow_nonneg (geometry.2.2.1.trans_le (moving_geometry hx).1).le 3) (sq_nonneg _))

theorem inner_derivative {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    HasDerivAt (innerPrimitive x) (logCubicKernel x y) y := by
  have hi := hasDerivAt_id y
  have h := (((((((((((hasDerivAt_log hy).const_mul (A0 x)).add (((hi.pow 1).const_mul (A1 x)).div_const 1)).add (((hi.pow 2).const_mul (A2 x)).div_const 2)).add (((hi.pow 3).const_mul (A3 x)).div_const 3)).add (((hi.pow 4).const_mul (A4 x)).div_const 4)).add (((hi.pow 5).const_mul (A5 x)).div_const 5)).add (((hi.pow 6).const_mul (A6 x)).div_const 6)).add (((hi.pow 7).const_mul (A7 x)).div_const 7)).add (((hi.pow 8).const_mul (A8 x)).div_const 8)).add (((hi.pow 9).const_mul (A9 x)).div_const 9)).const_mul (2/(3*x))
  convert h using 1 <;> first
  | rfl
  | (funext t; dsimp [innerPrimitive,polynomialPart]; ring)
  | (unfold logCubicKernel; rw [mul_assoc (2/3),numerator_expansion]; dsimp; field_simp [hx,hy]; ring)

theorem inner_integrable {x : ℝ} (hx : x ∈ Icc a b) :
    IntervalIntegrable (logCubicKernel x) volume b (lam-x) := by
  apply ContinuousOn.intervalIntegrable
  have hn (y : ℝ) (hy : y ∈ uIcc b (lam-x)) : x*y ≠ 0 := by
    rw [uIcc_of_le (moving_geometry hx).1] at hy
    exact mul_ne_zero (geometry.1.trans_le hx.1).ne' (geometry.2.2.1.trans_le hy.1).ne'
  unfold logCubicKernel SixthReciprocalCorrection.cubic
  apply ContinuousOn.div _ (by fun_prop) hn
  fun_prop

theorem inner_ftc {x : ℝ} (hx : x ∈ Icc a b) :
    (∫ y in b..lam-x, logCubicKernel x y) = movingLogCubic x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (inner_integrable hx)
  intro y hy
  rw [uIcc_of_le (moving_geometry hx).1] at hy
  exact inner_derivative (geometry.1.trans_le hx.1).ne' (geometry.2.2.1.trans_le hy.1).ne'

theorem movingLogCubic_eq {x : ℝ} (hx : x ∈ Icc a b) :
    movingLogCubic x = (2/(3*x))*(A0 x*log ((lam-x)/b)+polynomialPart x (lam-x)-polynomialPart x b) := by
  rw [log_div (geometry.2.2.1.trans_le (moving_geometry hx).1).ne' geometry.2.2.1.ne']
  unfold movingLogCubic innerPrimitive
  ring

theorem movingLogCubic_integrable : IntervalIntegrable movingLogCubic volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hn (x : ℝ) (hx : x ∈ uIcc a b) : x ≠ 0 :=
    (geometry.1.trans_le (uIcc_of_le geometry.2.1 ▸ hx).1).ne'
  have hq (x : ℝ) (hx : x ∈ uIcc a b) : lam-x ≠ 0 :=
    (geometry.2.2.1.trans_le (moving_geometry (uIcc_of_le geometry.2.1 ▸ hx)).1).ne'
  have hi := continuousOn_id.inv₀ hn
  have hl : ContinuousOn (fun x : ℝ => log (lam-x)) (uIcc a b) :=
    (continuousOn_const.sub continuousOn_id).log hq
  unfold movingLogCubic innerPrimitive polynomialPart A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 Q0 Q1 Q2 Q3 Q4 Q5 Q6 d0 d1 d2 d3
  simp only [div_eq_mul_inv,mul_inv_rev]
  fun_prop

/-- The three kernels share one actual comparison; the complement is paid once. -/
theorem actual_sixth_ge_joint :
    (4*∫ x in a..b, movingValue x + SixthReciprocalCorrection.movingCorrection x + movingLogCubic x) ≤
      truncatedSixthLowerF6lin := by
  have hc : Continuous (fun v : ℝ × ℝ => truncatedSixthZeroDeltaRegular 0 (v.1,v.2)) :=
    truncatedSixthZeroDelta_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun x : ℝ => ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral
      (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)) hc <;> fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      movingValue x + SixthReciprocalCorrection.movingCorrection x + movingLogCubic x ≤
        ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y) := by
    have hc1 := hc.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
    have hi := intervalIntegral.integral_mono_on (μ := volume) (moving_geometry hx).1
      (((moving_integrable hx).add (SixthReciprocalCorrection.inner_integrable hx)).add (inner_integrable hx))
      (hc1.intervalIntegrable b (lam-x)) (fun y hy => retained_joint_lower hx hy)
    rw [intervalIntegral.integral_add ((moving_integrable hx).add (SixthReciprocalCorrection.inner_integrable hx))
      (inner_integrable hx),intervalIntegral.integral_add (moving_integrable hx)
      (SixthReciprocalCorrection.inner_integrable hx),moving_ftc hx,
      SixthReciprocalCorrection.inner_ftc hx,inner_ftc hx] at hi
    have hn : 0 ≤ ∫ y in (lam-x)..s, truncatedSixthZeroDeltaRegular 0 (x,y) :=
      intervalIntegral.integral_nonneg (moving_geometry hx).2
        (fun y hy => ClassicalPositiveBounds.sixth_regular_nonneg hx
          ⟨(moving_geometry hx).1.trans hy.1,hy.2⟩)
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc1.intervalIntegrable b (lam-x)) (hc1.intervalIntegrable (lam-x) s)
    simp only [Function.comp_apply] at hi he
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    ((movingValue_integrable.add SixthReciprocalCorrection.movingCorrection_integrable).add
      movingLogCubic_integrable) (hinner.intervalIntegrable a b) hpoint
  have he := truncatedSixthZeroDelta_extension_eq (by norm_num : (0 : ℝ) ≤ 0)
  change (4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) = truncatedSixthLowerF6lin at he
  linarith

theorem movingLogCubic_zero_width {x : ℝ} (h : lam-x = b) : movingLogCubic x = 0 := by
  unfold movingLogCubic
  rw [h]
  exact sub_self _

theorem inner_integral_zero_width {x : ℝ} (h : lam-x = b) :
    (∫ y in b..lam-x, logCubicKernel x y) = 0 := by
  rw [h]
  exact intervalIntegral.integral_same

end Wu2008DoubleSieve.SixthLogCubicCorrection
