import JointSixthFourDiagnostic

namespace Wu2008DoubleSieve.FifthActualIntegralRecovery
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpMassBalance
open scoped Interval
noncomputable section

/-- These are the original full-triangle endpoints, not the sixth rectangle endpoints. -/
theorem parameter_range {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    s0 ≤ truncatedSixthLowerS 0 x y ∧ truncatedSixthLowerS 0 x y ≤ FifthClassicalShape.q := by
  constructor
  · apply (div_le_div_iff_of_pos_right truncatedSixthLower_parameters.1).2
    dsimp [s0,truncatedSixthLowerC]
    linarith [hxy.trans hy]
  · apply (div_le_div_iff_of_pos_right truncatedSixthLower_parameters.1).2
    dsimp [FifthClassicalShape.q,truncatedSixthLowerC]
    linarith [hx.trans hxy]

theorem parameters_exact : s0 = 70331/20600 ∧ FifthClassicalShape.q = 927/200 ∧
    3 < s0 ∧ s0 < 4 ∧ 4 < FifthClassicalShape.q ∧ FifthClassicalShape.q < 5 := by
  norm_num [s0,FifthClassicalShape.q,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

def logRegular (x y : ℝ) : ℝ :=
  log (truncatedSixthMassClip (truncatedSixthLowerS 0 x y)-1)/
    (max a x*max a y*max (2*a) (1/2-x-y))

def logIntegral : ℝ := 4*∫ y in a..b, ∫ x in a..y, logRegular x y

theorem log_continuous : Continuous (fun v : ℝ × ℝ => logRegular v.1 v.2) := by
  unfold logRegular
  apply Continuous.div
  · apply Continuous.log
    · unfold truncatedSixthMassClip truncatedSixthLowerS truncatedSixthLowerC
      fun_prop
    · intro v
      have h := (truncatedSixthMass_clip_bounds (truncatedSixthLowerS 0 v.1 v.2)).1
      linarith
  · fun_prop
  · intro v
    have ha := truncatedSixthLower_parameters.1
    exact (mul_pos (mul_pos (ha.trans_le (le_max_left _ _))
      (ha.trans_le (le_max_left _ _)))
      ((mul_pos (by norm_num : (0:ℝ)<2) ha).trans_le (le_max_left _ _))).ne'

theorem log_literal {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    logRegular x y = log (truncatedSixthLowerS 0 x y-1)/(x*y*(1/2-x-y)) := by
  have h := fifthPair_region_bounds (by norm_num : (0:ℝ) ≤ 0) (by norm_num)
    (show (x,y) ∈ fifthPairRegion from ⟨hx,hxy,hy⟩)
  unfold logRegular
  rw [truncatedSixthMass_clip_eq h.2.2.2,max_eq_right hx,max_eq_right (hx.trans hxy)]
  have hz : 2*a ≤ 1/2-x-y := by simpa [truncatedSixthLowerC] using h.2.2.1
  rw [max_eq_right hz]

theorem actual_triangle : fifthPairFlin =
    4*∫ y in a..b, ∫ x in a..y, fifthPairRegular 0 (x,y) := by
  unfold fifthPairFlin fifthPairFdelta
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hy
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hy.1] at hx
  simpa [truncatedSixthLowerC] using (ClassicalPositiveBounds.fifth_regular_eq hx.1 hx.2 hy.2).symm

theorem log_full_triangle : logIntegral =
    4*∫ y in a..b, ∫ x in a..y, log ((1/2-x-y)/a-1)/(x*y*(1/2-x-y)) := by
  unfold logIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hy
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hy.1] at hx
  simpa [truncatedSixthLowerS,truncatedSixthLowerC] using log_literal hx.1 hx.2 hy.2

/-- The initial identity is only invoked where the original parameter is at most four. -/
theorem initial_exact {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b)
    (h4 : truncatedSixthLowerS 0 x y ≤ 4) : fifthPairRegular 0 (x,y) = logRegular x y := by
  rw [ClassicalPositiveBounds.fifth_regular_eq hx hxy hy,log_literal hx hxy hy]
  have h := ClassicalLossBottleneck.initial_exact
    (show 2 ≤ truncatedSixthLowerS 0 x y by linarith [(parameter_range hx hxy hy).1,parameters_exact.2.2.1]) h4
  congr 1
  linarith

def cap (y : ℝ) : ℝ :=
  (FifthClassicalShape.q-4-(y-a)/a)^3/(36*a^2*(1/2-2*a))

def capPrimitive (y : ℝ) : ℝ :=
  ((FifthClassicalShape.q-4)^3*(y-a)^2/2-
    (FifthClassicalShape.q-4)^2*(y-a)^3/a+
    3*(FifthClassicalShape.q-4)*(y-a)^4/(4*a^2)-(y-a)^5/(5*a^3))/
    (36*a^2*(1/2-2*a))

def recurrenceCap : ℝ := 4*(capPrimitive b-capPrimitive a)

theorem pointwise_distance {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    0 ≤ fifthPairRegular 0 (x,y)-logRegular x y ∧
      fifthPairRegular 0 (x,y)-logRegular x y ≤ cap y := by
  have ha := truncatedSixthLower_parameters.1
  have hp := parameter_range hx hxy hy
  have hs : 2 ≤ truncatedSixthLowerS 0 x y := by linarith [hp.1,parameters_exact.2.2.1]
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hz : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
    linarith [hxy.trans hy]
  have hd := mul_pos (mul_pos hx0 hy0) hz
  have hbase : 0 < a^2*(1/2-2*a) := by norm_num [a,truncatedSixthLowerAlpha]
  have hden : a^2*(1/2-2*a) ≤ x*y*(1/2-x-y) := by
    have h := ClassicalPositiveBounds.denominator_box ha.le ha.le hx (hx.trans hxy)
      (show x+2*y ≤ 1/2 by
        have hb : 3*b ≤ 1/2 := by norm_num [b,truncatedSixthLowerBeta]
        linarith [hxy.trans hy]) hxy
    nlinarith only [h]
  have hc0 : 0 ≤ FifthClassicalShape.q-4-(y-a)/a := by
    have hby : (y-a)/a ≤ (b-a)/a := div_le_div_of_nonneg_right (by linarith) ha.le
    have hb : 0 ≤ FifthClassicalShape.q-4-(b-a)/a := by
      norm_num [FifthClassicalShape.q,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
    linarith
  have hnum : wuLowerCoefficient (truncatedSixthLowerS 0 x y)-
      log (truncatedSixthLowerS 0 x y-1) ≤ (FifthClassicalShape.q-4-(y-a)/a)^3/36 := by
    by_cases h4 : truncatedSixthLowerS 0 x y ≤ 4
    · rw [ClassicalLossBottleneck.initial_exact hs h4]
      positivity
    · have hr := ClassicalLossBottleneck.lower_recurrence_cap (le_of_not_ge h4)
        (hp.2.trans parameters_exact.2.2.2.2.2.le)
      have hh : truncatedSixthLowerS 0 x y-4 ≤ FifthClassicalShape.q-4-(y-a)/a := by
        calc
          _ ≤ (1/2-2*a-(y-a))/a-4 := sub_le_sub_right
            (div_le_div_of_nonneg_right (show 1/2-0-x-y ≤ 1/2-2*a-(y-a) by linarith) ha.le) 4
          _ = _ := by unfold FifthClassicalShape.q; rw [sub_div]; ring
      have hm := pow_le_pow_left₀ (show 0 ≤ truncatedSixthLowerS 0 x y-4 by linarith) hh 3
      linarith
  rw [ClassicalPositiveBounds.fifth_regular_eq hx hxy hy,log_literal hx hxy hy,← sub_div]
  refine ⟨div_nonneg (sub_nonneg.mpr (lower_ge_log hs)) hd.le,?_⟩
  have h := (div_le_div_of_nonneg_right hnum hd.le).trans
    (div_le_div_of_nonneg_left (by positivity) hbase hden)
  simpa only [cap,div_div,mul_assoc] using h

theorem cap_derivative (y : ℝ) : HasDerivAt capPrimitive ((y-a)*cap y) y := by
  have h := ((((((hasDerivAt_id y).sub_const a).pow 2).const_mul ((FifthClassicalShape.q-4)^3)).div_const 2).sub
    (((((hasDerivAt_id y).sub_const a).pow 3).const_mul ((FifthClassicalShape.q-4)^2)).div_const a)).add
    (((((hasDerivAt_id y).sub_const a).pow 4).const_mul (3*(FifthClassicalShape.q-4))).div_const (4*a^2))
  have hh := (h.sub (((((hasDerivAt_id y).sub_const a).pow 5)).div_const (5*a^3))).div_const (36*a^2*(1/2-2*a))
  convert hh using 1 <;> first | rfl |
    (dsimp [cap]; field_simp [truncatedSixthLower_parameters.1.ne']; ring)

theorem recurrenceCap_exact : recurrenceCap =
    162637585490910229451/99039473683301376000000 ∧ recurrenceCap < 1/500 := by
  norm_num [recurrenceCap,capPrimitive,FifthClassicalShape.q,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

/-- Distance from the complete elementary-log integral to the actual canonical coefficient. -/
theorem integral_distance : 0 ≤ fifthPairFlin-logIntegral ∧
    fifthPairFlin-logIntegral ≤ recurrenceCap := by
  have ha := truncatedSixthLower_parameters
  have hc : Continuous (fun v : ℝ × ℝ => fifthPairRegular 0 (v.1,v.2)) :=
    fifthPair_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hd := hc.sub log_continuous
  have hm (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
      Continuous (fun y : ℝ => ∫ x in a..y, f (x,y)) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => f (x,y))
    · exact hf.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hn : 0 ≤ ∫ y in a..b, ∫ x in a..y, fifthPairRegular 0 (x,y)-logRegular x y := by
    apply intervalIntegral.integral_nonneg ha.2.1.le
    intro y hy
    apply intervalIntegral.integral_nonneg hy.1
    intro x hx
    exact (pointwise_distance hx.1 hx.2 hy.2).1
  have hup : (∫ y in a..b, ∫ x in a..y, fifthPairRegular 0 (x,y)-logRegular x y) ≤
      ∫ y in a..b, (y-a)*cap y := by
    apply intervalIntegral.integral_mono_on ha.2.1.le (hm _ hd |>.intervalIntegrable a b)
      ((by unfold cap; fun_prop : Continuous (fun y : ℝ => (y-a)*cap y)).intervalIntegrable a b)
    intro y hy
    have h := intervalIntegral.integral_mono_on (μ := volume) hy.1
      ((hd.comp (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y)
      (intervalIntegrable_const (c := cap y)) (fun x hx => (pointwise_distance hx.1 hx.2 hy.2).2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,Function.comp_apply] using h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => cap_derivative y)
    ((by unfold cap; fun_prop : Continuous (fun y : ℝ => (y-a)*cap y)).intervalIntegrable a b)] at hup
  have he : fifthPairFlin-logIntegral =
      4*∫ y in a..b, ∫ x in a..y, fifthPairRegular 0 (x,y)-logRegular x y := by
    rw [actual_triangle]
    have hin (y : ℝ) := intervalIntegral.integral_sub (μ := volume)
      ((hc.comp (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y)
      ((log_continuous.comp (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y)
    simp only [Function.comp_apply] at hin
    simp_rw [hin]
    rw [intervalIntegral.integral_sub (hm _ hc |>.intervalIntegrable a b)
      (hm _ log_continuous |>.intervalIntegrable a b)]
    unfold logIntegral
    ring
  rw [he]
  unfold recurrenceCap
  constructor <;> linarith only [hn,hup]

/-- The restored log loss accounts for the entire fifth loss up to a proved rational distance. -/
def recovery : ℝ := logIntegral-AnalyticTotalThreshold.fifthEndpoint

theorem fifth_loss_localization : recovery ≤ AnalyticTotalThreshold.fifthLoss ∧
    AnalyticTotalThreshold.fifthLoss ≤ recovery+recurrenceCap := by
  have h := integral_distance
  unfold recovery AnalyticTotalThreshold.fifthLoss
  constructor <;> linarith only [h.1,h.2]

/-- Spend only the fifth loss; the other six original errors retain their signs and weights. -/
def coefficient : ℝ := JointSixthFourDiagnostic.coefficient+recovery/4

theorem coefficient_le_actual : coefficient ≤ JointHMotherPayment.unroundedCoefficient := by
  have hgap := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at hgap
  have hs := AnalyticTotalThreshold.signed_losses_nonnegative
  have hj := JointJLossStrength.actual_jLoss_lower
  have h6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.1
  have h4 := FourActualCapRecovery.actual_fourLoss_lower
  have h5 := fifth_loss_localization.1
  unfold coefficient JointSixthFourDiagnostic.coefficient ClassicalLossBottleneck.recoveredCoefficient
  unfold AnalyticTotalThreshold.sixthLoss at hgap h6
  linarith only [hgap,hs.1,hs.2.1,hs.2.2.2,hj,h6,h4,h5]

theorem seven_error_identity : JointHMotherPayment.unroundedCoefficient-coefficient =
    (AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+
      (AnalyticTotalThreshold.jLoss-JointJLossStrength.recovery)+AnalyticTotalThreshold.sharedLoss+
      (fifthPairFlin-logIntegral)+
      (truncatedSixthLowerF6lin-ClassicalLossBottleneck.sixthLogIntegral)+
      (AnalyticTotalThreshold.fourLoss-FourActualCapRecovery.recovery))/4 := by
  have h := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at h
  unfold coefficient JointSixthFourDiagnostic.coefficient ClassicalLossBottleneck.recoveredCoefficient
    recovery AnalyticTotalThreshold.fifthLoss AnalyticTotalThreshold.sixthLoss at *
  linarith only [h]

theorem unpaid_fifth_quarter : 0 ≤ (fifthPairFlin-logIntegral)/4 ∧
    (fifthPairFlin-logIntegral)/4 < 1/2000 := by
  have h := integral_distance
  have hc := recurrenceCap_exact.2
  constructor <;> linarith only [h.1,h.2,hc]

open FifthClassicalShape SharpLogRecurrence

/-- Only the original cubic logarithm envelope is used at the fixed original endpoint. -/
def minimumGap : ℝ := lowerLog (4/3)+lowerLog (3/2)+lowerLog ((s0-1)/2)-lowerLog (s0-1)
def densityGain : ℝ := minimumGap/(b^2*(1/2-2*b))
def integralGain : ℝ := 2*(b-a)^2*densityGain

theorem gain_rational : 0 < minimumGap ∧ 1/200 < integralGain := by
  norm_num [minimumGap,integralGain,densityGain,lowerLog,s0,a,b,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem gap_lower {t : ℝ} (ht : s0-1 ≤ t) : minimumGap ≤ log t-lowerLog t := by
  have h0 : 1 ≤ s0-1 := by linarith [parameters_exact.2.2.1]
  have h1 := log_lower (by norm_num : (1:ℝ) ≤ 4/3)
  have h2 := log_lower (by norm_num : (1:ℝ) ≤ 3/2)
  have h3 := log_lower (show 1 ≤ (s0-1)/2 by linarith [parameters_exact.2.2.1])
  have he2 : log (2:ℝ) = log (4/3:ℝ)+log (3/2:ℝ) := by
    rw [← log_mul (by norm_num : (4/3:ℝ) ≠ 0) (by norm_num : (3/2:ℝ) ≠ 0)]
    norm_num
  have he : log (s0-1) = log 2+log ((s0-1)/2) := by
    rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (show (s0-1)/2 ≠ 0 by linarith)]
    congr 1
    ring
  have hm := SixthLogTotalMagnitude.lower_gap_monotone h0 (h0.trans ht) ht
  unfold minimumGap
  linarith only [h1,h2,h3,he2,he,hm]

/-- The old affine shape lies below the original rational kernel, before any log replacement. -/
theorem shape_le_rational {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    shapeKernel x y ≤ lowerLog (truncatedSixthLowerS 0 x y-1)/(x*y*(1/2-x-y)) := by
  have ha := truncatedSixthLower_parameters.1
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hp := parameter_range hx hxy hy
  have hf := f_chord hp.1 hp.2
  have hh := div_le_div_of_nonneg_right hf (mul_pos ha (mul_pos hx0 hy0)).le
  have hz : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
    linarith [hxy.trans hy]
  have hz' : 1-x*2-y*2 ≠ 0 := by linarith
  convert hh using 1 <;> first | rfl |
    (simp only [shapeKernel,fifthDensity,f,s0,truncatedSixthLowerS,truncatedSixthLowerC,sub_zero]
     field_simp [ha.ne',hx0.ne',hy0.ne',hz.ne',hz']
     <;> ring)

theorem shape_log_distance {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    shapeKernel x y ≤ logRegular x y-densityGain := by
  have ha := truncatedSixthLower_parameters.1
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hz : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
    linarith [hxy.trans hy]
  have hd := mul_pos (mul_pos hx0 hy0) hz
  have hden : x*y*(1/2-x-y) ≤ b^2*(1/2-2*b) := by
    have h := ClassicalPositiveBounds.denominator_box hx0.le hy0.le (hxy.trans hy) hy
      (show b+2*b ≤ 1/2 by norm_num [b,truncatedSixthLowerBeta]) le_rfl
    nlinarith only [h]
  have hq := shape_le_rational hx hxy hy
  have hg := div_le_div_of_nonneg_right (gap_lower (show s0-1 ≤ truncatedSixthLowerS 0 x y-1 by
    linarith [(parameter_range hx hxy hy).1])) hd.le
  have hc := div_le_div_of_nonneg_left gain_rational.1.le hd hden
  rw [sub_div] at hg
  rw [log_literal hx hxy hy]
  unfold densityGain
  linarith only [hq,hg,hc]

theorem recovery_lower : integralGain ≤ recovery := by
  have hp := truncatedSixthLower_parameters
  have hc : Continuous (fun v : ℝ × ℝ => logRegular v.1 v.2-densityGain) :=
    log_continuous.sub continuous_const
  have hinner : Continuous (fun y : ℝ => ∫ x in a..y, logRegular x y-densityGain) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => logRegular x y-densityGain)
    · exact hc.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hn (y : ℝ) (hy : y ∈ uIcc a b) : y ≠ 0 := by
    rw [uIcc_of_le hp.2.1.le] at hy
    exact (hp.1.trans_le hy.1).ne'
  have hil : ContinuousOn (fun y : ℝ => log y-log a) (uIcc a b) :=
    (continuousOn_id.log (fun y hy => hn y hy)).sub continuousOn_const
  have hi0 : IntervalIntegrable innerShape volume a b := by
    apply ContinuousOn.intervalIntegrable
    unfold innerShape
    exact (((continuousOn_const.add (continuousOn_const.mul
      (continuousOn_const.sub continuousOn_id))).mul hil).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).div
      continuousOn_id (fun y hy => hn y hy)
  have hpoint (y : ℝ) (hy : y ∈ Icc a b) :
      innerShape y ≤ ∫ x in a..y, logRegular x y-densityGain := by
    rw [← inner_integral hy.1]
    have hy0 := hp.1.trans_le hy.1
    have hi : IntervalIntegrable (fun x => shapeKernel x y) volume a y := by
      apply ContinuousOn.intervalIntegrable
      unfold shapeKernel
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        rw [uIcc_of_le hy.1] at hx
        exact mul_ne_zero (hp.1.trans_le hx.1).ne' hy0.ne'
    exact intervalIntegral.integral_mono_on hy.1 hi
      ((hc.comp (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y)
      (fun x hx => shape_log_distance hx.1 hx.2 hy.2)
  have hi := intervalIntegral.integral_mono_on hp.2.1.le hi0 (hinner.intervalIntegrable a b) hpoint
  have hd (y : ℝ) (hy : y ∈ uIcc a b) : HasDerivAt primitive (innerShape y) y := by
    rw [uIcc_of_le hp.2.1.le] at hy
    exact primitive_derivative hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi0] at hi
  have hlog : Continuous (fun y : ℝ => ∫ x in a..y, logRegular x y) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => logRegular x y)
    · exact log_continuous.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hin (y : ℝ) : (∫ x in a..y, logRegular x y-densityGain) =
      (∫ x in a..y, logRegular x y)-(y-a)*densityGain := by
    have h := intervalIntegral.integral_sub (μ := volume)
      ((log_continuous.comp (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y)
      (intervalIntegrable_const (c := densityGain))
    simpa only [Function.comp_apply,intervalIntegral.integral_const,smul_eq_mul] using h
  simp_rw [hin] at hi
  rw [intervalIntegral.integral_sub (hlog.intervalIntegrable a b)
    ((by fun_prop : Continuous (fun y : ℝ => (y-a)*densityGain)).intervalIntegrable a b)] at hi
  have hcftc : (∫ y in a..b, (y-a)*densityGain) = (b-a)^2*densityGain/2 := by
    have hd (y : ℝ) (_hy : y ∈ uIcc a b) :
        HasDerivAt (fun y : ℝ => (y-a)^2*densityGain/2) ((y-a)*densityGain) y := by
      convert (((((hasDerivAt_id y).sub_const a).pow 2).mul_const densityGain).div_const 2) using 1 <;>
        first | rfl | (dsimp; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous (fun y : ℝ => (y-a)*densityGain)).intervalIntegrable a b)]
    ring
  rw [hcftc] at hi
  unfold integralGain recovery logIntegral AnalyticTotalThreshold.fifthEndpoint
  dsimp [primitive] at hi
  linarith only [hi]

theorem actual_fifth_loss_lower : 1/200 < AnalyticTotalThreshold.fifthLoss :=
  gain_rational.2.trans_le (recovery_lower.trans fifth_loss_localization.1)

theorem strict_parent_gain : JointSixthFourDiagnostic.coefficient+1/800 < coefficient := by
  have h := gain_rational.2.trans_le recovery_lower
  unfold coefficient
  linarith only [h]

/-- The unestimated recurrence tail is smaller than one third of a proved log recovery. -/
theorem recurrence_smaller_than_recovery : 3*recurrenceCap < integralGain := by
  norm_num [recurrenceCap,capPrimitive,integralGain,densityGain,minimumGap,
    FifthClassicalShape.q,lowerLog,s0,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

/-- The elementary-log replacement recovers more than three quarters of the actual fifth loss. -/
theorem recovered_fraction : (3/4)*AnalyticTotalThreshold.fifthLoss < recovery := by
  have h := fifth_loss_localization.2
  have hR := recovery_lower
  have hc := recurrence_smaller_than_recovery
  linarith only [h,hR,hc]

/-- Quantified localization: not merely the sign of a new lower certificate. -/
theorem fifth_loss_magnitude : 1/200 < recovery ∧ recovery ≤ AnalyticTotalThreshold.fifthLoss ∧
    AnalyticTotalThreshold.fifthLoss < recovery+1/500 ∧
    (3/4)*AnalyticTotalThreshold.fifthLoss < recovery := by
  have h := fifth_loss_localization
  refine ⟨gain_rational.2.trans_le recovery_lower,h.1,?_,recovered_fraction⟩
  linarith only [h.2,recurrenceCap_exact.2]

end
end Wu2008DoubleSieve.FifthActualIntegralRecovery
