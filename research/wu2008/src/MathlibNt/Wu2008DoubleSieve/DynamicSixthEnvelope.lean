import MathlibNt.Wu2008DoubleSieve.VariableCoefficientBalance

namespace Wu2008DoubleSieve.DynamicSixthEnvelope
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpMassBalance
open PositiveSixthFTC
open scoped Interval

 theorem moving_geometry {x : ℝ} (hx : x ∈ Icc a b) :
    b ≤ lam-x ∧ lam-x ≤ s := by
  have hg := geometry
  have hm : m = lam-b := rfl
  have he : s = lam-a := by
    norm_num [s,lam,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  constructor <;> linarith [hx.1,hx.2,hg.2.2.2.1]

/-- The lower polynomial is valid on the complete retained mask, not just a fixed rectangle. -/
 theorem retained_polynomial_lower {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    polynomialKernel x y ≤ truncatedSixthZeroDeltaRegular 0 (x,y) := by
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
  have ht := mul_le_mul_of_nonneg_left (reciprocal_square_tangent hz)
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd) (mul_pos hb.1 hb.2.1).le)
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx ⟨hy.1,hys⟩,if_pos hr]
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

noncomputable def movingValue (x : ℝ) : ℝ := innerPrimitive x (lam-x)-innerPrimitive x b

 theorem moving_integrable {x : ℝ} (hx : x ∈ Icc a b) :
    IntervalIntegrable (polynomialKernel x) volume b (lam-x) := by
  apply ContinuousOn.intervalIntegrable
  have hn (y : ℝ) (hy : y ∈ uIcc b (lam-x)) : y ≠ 0 := by
    rw [uIcc_of_le (moving_geometry hx).1] at hy
    exact (geometry.2.2.1.trans_le hy.1).ne'
  unfold polynomialKernel
  simp only [div_mul_eq_div_div]
  exact (by fun_prop : ContinuousOn (fun y : ℝ => 128*(lam-x-y)*(2*x+2*y-1/4)/x)
    (uIcc b (lam-x))).div continuousOn_id hn

 theorem moving_ftc {x : ℝ} (hx : x ∈ Icc a b) :
    (∫ y in b..lam-x, polynomialKernel x y) = movingValue x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (moving_integrable hx)
  intro y hy
  rw [uIcc_of_le (moving_geometry hx).1] at hy
  exact inner_derivative (geometry.1.trans_le hx.1).ne'
    (geometry.2.2.1.trans_le hy.1).ne'

 theorem movingValue_integrable : IntervalIntegrable movingValue volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hn (x : ℝ) (hx : x ∈ uIcc a b) : x ≠ 0 := by
    rw [uIcc_of_le geometry.2.1] at hx
    exact (geometry.1.trans_le hx.1).ne'
  have hm (x : ℝ) (hx : x ∈ uIcc a b) : lam-x ≠ 0 := by
    rw [uIcc_of_le geometry.2.1] at hx
    exact (geometry.2.2.1.trans_le (moving_geometry hx).1).ne'
  have hl : ContinuousOn (fun x : ℝ => log (lam-x)) (uIcc a b) :=
    (continuousOn_const.sub continuousOn_id).log hm
  have hi : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc a b) := continuousOn_id.inv₀ hn
  have hi4 : ContinuousOn (fun x : ℝ => (4*x)⁻¹) (uIcc a b) :=
    (continuousOn_id.const_mul 4).inv₀ (fun x hx => mul_ne_zero (by norm_num) (hn x hx))
  unfold movingValue innerPrimitive
  simp only [div_eq_mul_inv]
  fun_prop

 theorem actual_sixth_ge_moving :
    (4*∫ x in a..b, movingValue x) ≤ truncatedSixthLowerF6lin := by
  have hc : Continuous (fun v : ℝ × ℝ => truncatedSixthZeroDeltaRegular 0 (v.1,v.2)) :=
    truncatedSixthZeroDelta_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun x : ℝ => ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral
      (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)) hc <;> fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) : movingValue x ≤
      ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y) := by
    have hc1 := hc.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
    have hi := intervalIntegral.integral_mono_on (μ := volume) (moving_geometry hx).1
      (moving_integrable hx) (hc1.intervalIntegrable b (lam-x))
      (fun y hy => retained_polynomial_lower hx hy)
    rw [moving_ftc hx] at hi
    have hn : 0 ≤ ∫ y in (lam-x)..s, truncatedSixthZeroDeltaRegular 0 (x,y) :=
      intervalIntegral.integral_nonneg (moving_geometry hx).2
        (fun y hy => ClassicalPositiveBounds.sixth_regular_nonneg hx
          ⟨(moving_geometry hx).1.trans hy.1,hy.2⟩)
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc1.intervalIntegrable b (lam-x)) (hc1.intervalIntegrable (lam-x) s)
    simp only [Function.comp_apply] at hi he
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    movingValue_integrable (hinner.intervalIntegrable a b) hpoint
  have he := truncatedSixthZeroDelta_extension_eq (by norm_num : (0 : ℝ) ≤ 0)
  change (4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) =
    truncatedSixthLowerF6lin at he
  linarith

/-- The logarithm at the moving boundary has a negative coefficient throughout the original x range. -/
 theorem moving_log_coefficient_nonpos {x : ℝ} (hx : x ∈ Icc a b) :
    128*(lam-x)*(2-1/(4*x)) ≤ 0 := by
  have hx0 := geometry.1.trans_le hx.1
  have hx8 : x ≤ 1/8 := by
    have hb8 : b ≤ 1/8 := by norm_num [b,truncatedSixthLowerBeta]
    exact hx.2.trans hb8
  have hd : 2-1/(4*x) ≤ 0 := by
    have h : (2 : ℝ) ≤ 1/(4*x) := (le_div_iff₀ (mul_pos (by norm_num) hx0)).2 (by linarith)
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by norm_num) ((geometry.2.2.1.trans_le (moving_geometry hx).1).le)) hd

/-- No target-shaped hypothesis: the complete coefficient consumes the whole-mask FTC leaf. -/
 theorem complete_coefficient_gt_moving_balance :
    54035471/1012500+3/2+(4*∫ x in a..b, movingValue x)+47/481250-
      VariableCoefficientBalance.rationalG-12-21/20 <
      TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := SharpSingleBalance.base_sharp_lower
  have hg := VariableCoefficientBalance.full_G_rational
  have hj := SharpJBalance.weighted_J_lt_twelve
  have h4 := SharpMassBalance.four_weighted_lt_21_twentieths
  have hp := SharpMassBalance.fifth_gt_three_halves
  have hq := actual_sixth_ge_moving
  change SingleUpperClassicalLimit.Glin (1/3)+
    SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma ≤ VariableCoefficientBalance.rationalG at hg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient
  linarith

end Wu2008DoubleSieve.DynamicSixthEnvelope
