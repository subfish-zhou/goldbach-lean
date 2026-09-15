import MathlibNt.Wu2008DoubleSieve.RationalMovingSixth

namespace Wu2008DoubleSieve.SixthReciprocalCorrection
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope
open scoped Interval

noncomputable def cubic (z : ℝ) : ℝ := 16*(1-2*(4*z-1)+3*(4*z-1)^2-4*(4*z-1)^3)
noncomputable def correction (z : ℝ) : ℝ := 16*(4*z-1)^2*(7-16*z)

/-- Exact remainder at the original quarter, valid on the whole positive ray. -/
theorem cubic_remainder {z : ℝ} (hz : 0 < z) :
    1/z^2-cubic z = 16*(4*z-1)^4*(5+4*(4*z-1))/(1+(4*z-1))^2 := by
  have hh : 1+(4*z-1) ≠ 0 := by linarith
  unfold cubic
  field_simp [hz.ne',hh]
  ring

theorem cubic_lower {z : ℝ} (hz : 0 < z) : cubic z ≤ 1/z^2 := by
  have h : 0 ≤ 16*(4*z-1)^4*(5+4*(4*z-1))/(1+(4*z-1))^2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (by linarith)) (sq_nonneg _)
  rw [← cubic_remainder hz] at h
  linarith

theorem correction_difference (z : ℝ) : cubic z-(48-128*z) = correction z := by
  unfold cubic correction
  ring

theorem retained_z_bounds {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (lam-x)) :
    2*a ≤ 1/2-x-y ∧ 1/2-x-y ≤ 1/2-a-b ∧ 1/2-a-b < 7/16 := by
  have hlast : (1/2-a-b : ℝ) < 7/16 := by
    norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  dsimp [lam] at hy
  constructor
  · linarith [hy.2]
  constructor
  · linarith [hx.1,hy.1]
  · exact hlast

theorem correction_nonneg {z : ℝ} (hz : z ≤ 7/16) : 0 ≤ correction z := by
  unfold correction
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith)

noncomputable def correctionKernel (x y : ℝ) : ℝ :=
  2*(lam-x-y)*correction (1/2-x-y)/(x*y)

theorem correctionKernel_nonneg {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (lam-x)) :
    0 ≤ correctionKernel x y := by
  have hz := retained_z_bounds hx hy
  unfold correctionKernel
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hy.2]))
    (correction_nonneg (hz.2.1.trans hz.2.2.le)))
    (mul_pos (geometry.1.trans_le hx.1) (geometry.2.2.1.trans_le hy.1)).le
 theorem retained_joint_lower {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    polynomialKernel x y + correctionKernel x y ≤ truncatedSixthZeroDeltaRegular 0 (x,y) := by
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
  have hd : 0 ≤ lam-x-y := by linarith [hy.2]
  have ht := mul_le_mul_of_nonneg_left (cubic_lower hz)
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd) (mul_pos hb.1 hb.2.1).le)
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx ⟨hy.1,hys⟩,if_pos hr]
  simp only [truncatedSixthLowerC, sub_zero]
  change _ ≤ wuLowerCoefficient (truncatedSixthLowerS 0 x y)/(x*y*(1/2-x-y))
  calc
    polynomialKernel x y + correctionKernel x y = (2*(lam-x-y)/(x*y))*cubic (1/2-x-y) := by
      dsimp [polynomialKernel,correctionKernel,correction,cubic]; ring
    _ ≤ (2*(lam-x-y)/(x*y))*(1/(1/2-x-y)^2) := ht
    _ = (2*(truncatedSixthLowerS 0 x y-2)/truncatedSixthLowerS 0 x y)/(x*y*(1/2-x-y)) := by
      have hz' : 1-x*2-y*2 ≠ 0 := by linarith
      simp only [truncatedSixthLowerS,truncatedSixthLowerC,lam,sub_zero]
      field_simp [hp.1.ne',hb.1.ne',hb.2.1.ne',hz.ne',hz']; ring
    _ ≤ _ := hdiv

noncomputable def d0 (x : ℝ) : ℝ := 4096*x^3-2304*x^2+384*x-16
noncomputable def d1 (x : ℝ) : ℝ := 12288*x^2-4608*x+384
noncomputable def d2 (x : ℝ) : ℝ := 12288*x-2304
noncomputable def A0 (x : ℝ) : ℝ := (lam-x)*d0 x
noncomputable def A1 (x : ℝ) : ℝ := (lam-x)*d1 x-d0 x
noncomputable def A2 (x : ℝ) : ℝ := (lam-x)*d2 x-d1 x
noncomputable def A3 (x : ℝ) : ℝ := (lam-x)*4096-d2 x
noncomputable def polynomialPart (x y : ℝ) : ℝ := A1 x*y+A2 x*y^2/2+A3 x*y^3/3-1024*y^4
noncomputable def innerPrimitive (x y : ℝ) : ℝ := (2/x)*(A0 x*log y+polynomialPart x y)
noncomputable def movingCorrection (x : ℝ) : ℝ := innerPrimitive x (lam-x)-innerPrimitive x b

theorem correction_initial (x : ℝ) : correction (1/2-x) = d0 x := by
  unfold correction d0
  ring

theorem initial_nonneg {x : ℝ} (hx : x ∈ Icc a b) : 0 ≤ d0 x := by
  have ha : (1/16 : ℝ) < a := by norm_num [a,truncatedSixthLowerAlpha]
  have he : d0 x = 16*(1-4*x)^2*(16*x-1) := by unfold d0; ring
  rw [he]
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith [hx.1])

theorem moving_log_coefficient_nonneg {x : ℝ} (hx : x ∈ Icc a b) : 0 ≤ (2/x)*A0 x := by
  unfold A0
  exact mul_nonneg (div_nonneg (by norm_num) (geometry.1.trans_le hx.1).le)
    (mul_nonneg (geometry.2.2.1.trans_le (moving_geometry hx).1).le (initial_nonneg hx))

theorem inner_derivative {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    HasDerivAt (innerPrimitive x) (correctionKernel x y) y := by
  have hi := hasDerivAt_id y
  have h := ((((((hasDerivAt_log hy).const_mul (A0 x)).add (hi.const_mul (A1 x))).add
    (((hi.pow 2).const_mul (A2 x)).div_const 2)).add
    (((hi.pow 3).const_mul (A3 x)).div_const 3)).sub ((hi.pow 4).const_mul 1024)).const_mul (2/x)
  convert h using 1 <;> first
  | rfl
  | (funext t; dsimp [innerPrimitive,polynomialPart]; ring)
  | (dsimp [correctionKernel,correction,A0,A1,A2,A3,d0,d1,d2]; field_simp [hx,hy]; ring)

theorem inner_integrable {x : ℝ} (hx : x ∈ Icc a b) :
    IntervalIntegrable (correctionKernel x) volume b (lam-x) := by
  apply ContinuousOn.intervalIntegrable
  have hn (y : ℝ) (hy : y ∈ uIcc b (lam-x)) : x*y ≠ 0 := by
    rw [uIcc_of_le (moving_geometry hx).1] at hy
    exact mul_ne_zero (geometry.1.trans_le hx.1).ne' (geometry.2.2.1.trans_le hy.1).ne'
  unfold correctionKernel correction
  exact (by fun_prop : ContinuousOn (fun y : ℝ => 2*(lam-x-y)*(16*(4*(1/2-x-y)-1)^2*(7-16*(1/2-x-y))))
    (uIcc b (lam-x))).div (by fun_prop) hn

theorem inner_ftc {x : ℝ} (hx : x ∈ Icc a b) :
    (∫ y in b..lam-x, correctionKernel x y) = movingCorrection x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (inner_integrable hx)
  intro y hy
  rw [uIcc_of_le (moving_geometry hx).1] at hy
  exact inner_derivative (geometry.1.trans_le hx.1).ne' (geometry.2.2.1.trans_le hy.1).ne'

theorem movingCorrection_eq {x : ℝ} (hx : x ∈ Icc a b) :
    movingCorrection x = (2/x)*(A0 x*log ((lam-x)/b)+polynomialPart x (lam-x)-polynomialPart x b) := by
  rw [log_div (geometry.2.2.1.trans_le (moving_geometry hx).1).ne' geometry.2.2.1.ne']
  unfold movingCorrection innerPrimitive
  ring

theorem movingCorrection_integrable : IntervalIntegrable movingCorrection volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hn (x : ℝ) (hx : x ∈ uIcc a b) : x ≠ 0 :=
    (geometry.1.trans_le (uIcc_of_le geometry.2.1 ▸ hx).1).ne'
  have hq (x : ℝ) (hx : x ∈ uIcc a b) : lam-x ≠ 0 :=
    (geometry.2.2.1.trans_le (moving_geometry (uIcc_of_le geometry.2.1 ▸ hx)).1).ne'
  have hi := continuousOn_id.inv₀ hn
  have hl : ContinuousOn (fun x : ℝ => log (lam-x)) (uIcc a b) :=
    (continuousOn_const.sub continuousOn_id).log hq
  unfold movingCorrection innerPrimitive polynomialPart A0 A1 A2 A3 d0 d1 d2
  simp only [div_eq_mul_inv]
  fun_prop

/-- The original full mask and its nonnegative remainder are retained with outer weight four. -/
theorem actual_sixth_ge_joint :
    (4*∫ x in a..b, movingValue x + movingCorrection x) ≤ truncatedSixthLowerF6lin := by
  have hc : Continuous (fun v : ℝ × ℝ => truncatedSixthZeroDeltaRegular 0 (v.1,v.2)) :=
    truncatedSixthZeroDelta_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun x : ℝ => ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral
      (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)) hc <;> fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) : movingValue x + movingCorrection x ≤
      ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y) := by
    have hc1 := hc.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
    have hi := intervalIntegral.integral_mono_on (μ := volume) (moving_geometry hx).1
      ((moving_integrable hx).add (inner_integrable hx)) (hc1.intervalIntegrable b (lam-x))
      (fun y hy => retained_joint_lower hx hy)
    rw [intervalIntegral.integral_add (moving_integrable hx) (inner_integrable hx),
      moving_ftc hx,inner_ftc hx] at hi
    have hn : 0 ≤ ∫ y in (lam-x)..s, truncatedSixthZeroDeltaRegular 0 (x,y) :=
      intervalIntegral.integral_nonneg (moving_geometry hx).2
        (fun y hy => ClassicalPositiveBounds.sixth_regular_nonneg hx
          ⟨(moving_geometry hx).1.trans hy.1,hy.2⟩)
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc1.intervalIntegrable b (lam-x)) (hc1.intervalIntegrable (lam-x) s)
    simp only [Function.comp_apply] at hi he
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    (movingValue_integrable.add movingCorrection_integrable) (hinner.intervalIntegrable a b) hpoint
  have he := truncatedSixthZeroDelta_extension_eq (by norm_num : (0 : ℝ) ≤ 0)
  change (4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) =
    truncatedSixthLowerF6lin at he
  linarith

end Wu2008DoubleSieve.SixthReciprocalCorrection
