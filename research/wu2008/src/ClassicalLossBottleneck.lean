import JointLogTotalComparison

namespace Wu2008DoubleSieve.ClassicalLossBottleneck
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Interval
noncomputable section

/-- A true recurrence/FTC bound, not a Taylor extension of the log envelope. -/
theorem upper_recurrence_cap {u : ℝ} (hu : 3 ≤ u) (hu4 : u ≤ 4) :
    wuUpperCoefficient u ≤ 1+(u-3)^2/4 := by
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2:ℝ) ≤ 3) hu
  have he : wuUpperCoefficient 3 = 1 := jr1965F_normalized_initial (by norm_num) le_rfl
  have hab : 2 ≤ u-1 := by linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (wuLowerCoefficient_div_intervalIntegrable (by norm_num) hab)
    ((by fun_prop : Continuous (fun v : ℝ => (v-2)/2)).intervalIntegrable 2 (u-1))
    (fun v hv => show wuLowerCoefficient v/v ≤ (v-2)/2 from by
      have hv0 : 0 < v := by linarith [hv.1]
      rw [show wuLowerCoefficient v = log (v-1) from
        jr1965f_normalized_firstInterval hv.1 (by linarith [hv.2])]
      have hl := log_le_sub_one_of_pos (show 0 < v-1 by linarith [hv.1])
      apply (div_le_iff₀ hv0).2
      nlinarith [sq_nonneg (v-2)])
  have hf : (∫ v in (2:ℝ)..(u-1), (v-2)/2) = (u-3)^2/4 := by
    have hd (v : ℝ) (_hv : v ∈ uIcc 2 (u-1)) :
        HasDerivAt (fun v : ℝ => (v-2)^2/4) ((v-2)/2) v := by
      convert (((hasDerivAt_id v).sub_const 2).pow 2).div_const 4 using 1 <;>
        first | rfl | (dsimp; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous (fun v : ℝ => (v-2)/2)).intervalIntegrable 2 (u-1))]
    ring
  rw [hf] at hi
  norm_num only [show (3:ℝ)-1=2 by norm_num,he] at hr
  linarith

/-- Only the actual first recurrence beyond four is bounded. -/
theorem lower_recurrence_cap {v : ℝ} (hv : 4 ≤ v) (hv5 : v ≤ 5) :
    wuLowerCoefficient v-log (v-1) ≤ (v-4)^3/36 := by
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2:ℝ) ≤ 4) hv
  have hab : 3 ≤ v-1 := by linarith
  have hrecip : IntervalIntegrable (fun u : ℝ => 1/u) volume 3 (v-1) := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div continuousOn_id (fun u hu => by
      rw [uIcc_of_le hab] at hu
      change u ≠ 0
      linarith [hu.1])
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    ((wuUpperCoefficient_div_intervalIntegrable (by norm_num) hab).sub hrecip)
    ((by fun_prop : Continuous (fun u : ℝ => (u-3)^2/12)).intervalIntegrable 3 (v-1))
    (fun u hu => show wuUpperCoefficient u/u-1/u ≤ (u-3)^2/12 from by
      have hu0 : 0 < u := by linarith [hu.1]
      have hc := upper_recurrence_cap hu.1 (by linarith [hu.2])
      rw [← sub_div]
      apply (div_le_iff₀ hu0).2
      have hm := mul_nonneg (sq_nonneg (u-3)) (show 0 ≤ u-3 by linarith [hu.1])
      nlinarith)
  rw [intervalIntegral.integral_sub
    (wuUpperCoefficient_div_intervalIntegrable (by norm_num) hab) hrecip,
    integral_reciprocal (by norm_num) hab] at hi
  have hf : (∫ u in (3:ℝ)..(v-1), (u-3)^2/12) = (v-4)^3/36 := by
    have hd (u : ℝ) (_hu : u ∈ uIcc 3 (v-1)) :
        HasDerivAt (fun u : ℝ => (u-3)^3/36) ((u-3)^2/12) u := by
      convert (((hasDerivAt_id u).sub_const 3).pow 3).div_const 36 using 1 <;>
        first | rfl | (dsimp; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous (fun u : ℝ => (u-3)^2/12)).intervalIntegrable 3 (v-1))]
    ring
  rw [hf] at hi
  norm_num only [show (4:ℝ)-1=3 by norm_num,BaseRecurrenceLower.lower_four_value] at hr
  linarith

/-- The largest actual S in the original retained sixth region. -/
theorem sixth_parameter_cap {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b s) : truncatedSixthLowerS 0 x y ≤ 41453/10300 := by
  apply (div_le_iff₀ truncatedSixthLower_parameters.1).2
  have hxlo := hx.1
  have hylo := hy.1
  norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerC] at hxlo hylo ⊢
  linarith

/-- No beyond-initial recurrence correction is present below the original level four. -/
theorem initial_exact {v : ℝ} (hv : 2 ≤ v) (hv4 : v ≤ 4) :
    wuLowerCoefficient v-log (v-1) = 0 := by
  rw [show wuLowerCoefficient v = log (v-1) from jr1965f_normalized_firstInterval hv hv4]
  ring

/-- The recurrence surplus is uniformly tiny on the entire original S range. -/
theorem sixth_recurrence_uniform {v : ℝ} (hv : 2 ≤ v) (hvu : v ≤ 41453/10300) :
    0 ≤ wuLowerCoefficient v-log (v-1) ∧
      wuLowerCoefficient v-log (v-1) ≤ (253/10300)^3/36 := by
  refine ⟨sub_nonneg.mpr (lower_ge_log hv),?_⟩
  by_cases h4 : v ≤ 4
  · rw [initial_exact hv h4]
    norm_num
  · have h := lower_recurrence_cap (le_of_not_ge h4) (by linarith)
    have hp := pow_le_pow_left₀ (show 0 ≤ v-4 by linarith) (show v-4 ≤ 253/10300 by linarith) 3
    linarith

/-- The allegedly discarded complement has identically zero actual kernel. -/
theorem sixth_complement_zero {x y : ℝ} (_hx : x ∈ Icc a b)
    (hy : y ∈ Icc (lam-x) s) : truncatedSixthZeroDeltaRegular 0 (x,y) = 0 := by
  have hS : truncatedSixthLowerS 0 x y ≤ 2 := by
    apply (div_le_iff₀ truncatedSixthLower_parameters.1).2
    have h := hy.1
    dsimp [lam,truncatedSixthLowerC] at h ⊢
    linarith
  unfold truncatedSixthZeroDeltaRegular
  rw [truncatedSixthZeroDelta_clip_zero hS,zero_div]

/-- In particular the entire complement integral is exactly zero, not merely nonnegative. -/
theorem sixth_complement_integral_zero {x : ℝ} (hx : x ∈ Icc a b) :
    (∫ y in (lam-x)..s, truncatedSixthZeroDeltaRegular 0 (x,y)) = 0 := by
  calc
    _ = ∫ _y in (lam-x)..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact sixth_complement_zero hx (uIcc_of_le (moving_geometry hx).2 ▸ hy)
    _ = 0 := by simp

/-- Precise original moving-domain equality, with no extension of F6. -/
theorem sixth_actual_domain : truncatedSixthLowerF6lin =
    4*∫ x in a..b, ∫ y in b..(lam-x), truncatedSixthZeroDeltaRegular 0 (x,y) := by
  unfold truncatedSixthLowerF6lin
  rw [← truncatedSixthZeroDelta_extension_eq (by norm_num : (0:ℝ) ≤ 0)]
  unfold truncatedSixthZeroDeltaExtension
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le geometry.2.1] at hx
  have hc : Continuous (fun y => truncatedSixthZeroDeltaRegular 0 (x,y)) :=
    truncatedSixthZeroDelta_regular_continuous.comp (f := fun y : ℝ => (0,(x,y))) (by fun_prop)
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable b (lam-x)) (hc.intervalIntegrable (lam-x) s)
  rw [sixth_complement_integral_zero hx,add_zero] at h
  exact h.symm

/-- The initial log kernel uses exactly the original continuous clipping and denominator. -/
def sixthLogRegular (x y : ℝ) : ℝ :=
  log (truncatedSixthMassClip (truncatedSixthLowerS 0 x y)-1)/
    truncatedSixthMassDenominator 0 (x,y)

def sixthLogIntegral : ℝ := 4*∫ x in a..b, ∫ y in b..s, sixthLogRegular x y

def recurrenceKernelCap : ℝ := ((253/10300)^3/36)/(2*a^2*b)

 theorem sixth_log_continuous : Continuous (fun v : ℝ × ℝ => sixthLogRegular v.1 v.2) := by
  unfold sixthLogRegular
  apply Continuous.div
  · apply Continuous.log
    · unfold truncatedSixthMassClip truncatedSixthLowerS truncatedSixthLowerC
      fun_prop
    · intro v
      have h := (truncatedSixthMass_clip_bounds (truncatedSixthLowerS 0 v.1 v.2)).1
      linarith
  · unfold truncatedSixthMassDenominator truncatedSixthLowerC
    fun_prop
  · intro v
    exact (truncatedSixthMass_denominator_pos 0 v).ne'

 theorem sixth_log_pointwise {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b s) :
    0 ≤ truncatedSixthZeroDeltaRegular 0 (x,y)-sixthLogRegular x y ∧
      truncatedSixthZeroDeltaRegular 0 (x,y)-sixthLogRegular x y ≤ recurrenceKernelCap := by
  have hcap := sixth_parameter_cap hx hy
  have hc : truncatedSixthMassClip (truncatedSixthLowerS 0 x y) ≤ 41453/10300 := by
    unfold truncatedSixthMassClip
    exact max_le (by norm_num) ((min_le_right _ _).trans hcap)
  have h := sixth_recurrence_uniform
    (truncatedSixthMass_clip_bounds (truncatedSixthLowerS 0 x y)).1 hc
  have hd := truncatedSixthMass_denominator_pos 0 (x,y)
  have ha : 0 < a := geometry.1
  have hb : 0 < b := geometry.2.2.1
  have hlo : 2*a^2*b ≤ truncatedSixthMassDenominator 0 (x,y) := by
    have hxy : a*b ≤ max a x*max b y :=
      mul_le_mul (le_max_left _ _) (le_max_left _ _) hb.le
        (ha.le.trans (le_max_left _ _))
    have hz := mul_le_mul hxy (le_max_left (2*a) (truncatedSixthLowerC 0-x-y))
      (by positivity : 0 ≤ 2*a)
      (mul_nonneg (ha.le.trans (le_max_left _ _)) (hb.le.trans (le_max_left _ _)))
    change _ ≤ max a x*max b y*max (2*a) (truncatedSixthLowerC 0-x-y)
    nlinarith only [hz]
  unfold truncatedSixthZeroDeltaRegular sixthLogRegular
  rw [← sub_div]
  refine ⟨div_nonneg h.1 hd.le,?_⟩
  exact (div_le_div_of_nonneg_right h.2 hd.le).trans
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) hlo)

/-- An actual upper bound on the full sixth recurrence correction, not on a lower certificate. -/
theorem sixth_recurrence_integral_cap :
    0 ≤ truncatedSixthLowerF6lin-sixthLogIntegral ∧
      truncatedSixthLowerF6lin-sixthLogIntegral < 1/100000 := by
  have hc : Continuous (fun v : ℝ × ℝ =>
      truncatedSixthZeroDeltaRegular 0 (v.1,v.2)-sixthLogRegular v.1 v.2) :=
    (truncatedSixthZeroDelta_regular_continuous.comp
      (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)).sub sixth_log_continuous
  have hi : Continuous (fun x : ℝ => ∫ y in b..s,
      truncatedSixthZeroDeltaRegular 0 (x,y)-sixthLogRegular x y) := by
    apply gamma5Gain_moving_integral
      (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)-sixthLogRegular x y) hc <;> fun_prop
  have hp (x : ℝ) (hx : x ∈ Icc a b) :
      0 ≤ ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)-sixthLogRegular x y :=
    intervalIntegral.integral_nonneg truncatedSixthLower_parameters.2.2.1.le
      (fun y hy => (sixth_log_pointwise hx hy).1)
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      (∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)-sixthLogRegular x y) ≤
        (s-b)*recurrenceKernelCap := by
    have h := intervalIntegral.integral_mono_on (μ := volume) truncatedSixthLower_parameters.2.2.1.le
      ((hc.comp (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable b s)
      (intervalIntegrable_const (c := recurrenceKernelCap))
      (fun y hy => (sixth_log_pointwise hx hy).2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,Function.comp_apply] using h
  have hnon := intervalIntegral.integral_nonneg (μ := volume) geometry.2.1 hp
  have hup := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    (hi.intervalIntegrable a b) (intervalIntegrable_const (c := (s-b)*recurrenceKernelCap)) hpoint
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hup
  have hcont : Continuous (fun v : ℝ × ℝ => truncatedSixthZeroDeltaRegular 0 (v.1,v.2)) :=
    truncatedSixthZeroDelta_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have haI : Continuous (fun x : ℝ => ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)) hcont <;> fun_prop
  have hlI : Continuous (fun x : ℝ => ∫ y in b..s, sixthLogRegular x y) := by
    apply gamma5Gain_moving_integral (f := sixthLogRegular) sixth_log_continuous <;> fun_prop
  have he : truncatedSixthLowerF6lin-sixthLogIntegral =
      4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)-sixthLogRegular x y := by
    have haeq := truncatedSixthZeroDelta_extension_eq (by norm_num : (0:ℝ) ≤ 0)
    change (4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) =
      truncatedSixthLowerF6lin at haeq
    rw [← haeq]
    have hin (x : ℝ) := intervalIntegral.integral_sub (μ := volume)
      ((hcont.comp (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable b s)
      ((sixth_log_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable b s)
    simp only [Function.comp_apply] at hin
    simp_rw [hin]
    rw [intervalIntegral.integral_sub (haI.intervalIntegrable a b) (hlI.intervalIntegrable a b)]
    unfold sixthLogIntegral
    ring
  rw [he]
  have hn : 4*((b-a)*((s-b)*recurrenceKernelCap)) < (1/100000 : ℝ) := by
    norm_num [recurrenceKernelCap,a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]
  constructor <;> linarith

/-- Exact diagnosis: almost all possible sixth loss lies in the original log envelopes. -/
theorem sixth_loss_localization :
    sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint ≤ AnalyticTotalThreshold.sixthLoss ∧
    AnalyticTotalThreshold.sixthLoss <
      sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint+1/100000 := by
  have h := sixth_recurrence_integral_cap
  unfold AnalyticTotalThreshold.sixthLoss
  constructor <;> linarith

/-- Both original fourfold pieces are already joined, and the clipping at two is inactive. -/
theorem four_parameter_range {x y z t : ℝ} (hx : x ≤ FourRoughClosedMass.beta)
    (hy0 : FourRoughClosedMass.alpha ≤ y) (hy : y ≤ FourRoughClosedMass.beta)
    (ht : t ≤ FourRoughClosedMass.lam-z) :
    (10/3 : ℝ) < FourRoughClosedMass.parameter x y z t ∧
      max 2 (FourRoughClosedMass.parameter x y z t) = FourRoughClosedMass.parameter x y z t := by
  have hypos := FourRoughClosedMass.fixed_geometry.2.1.trans_le hy0
  have h : (10/3 : ℝ) < FourRoughClosedMass.parameter x y z t := by
    unfold FourRoughClosedMass.parameter
    apply (lt_div_iff₀ hypos).2
    have hc : 0 < 1-(16/3)*FourRoughClosedMass.beta-FourRoughClosedMass.lam := by
      norm_num [FourRoughClosedMass.beta,FourRoughClosedMass.lam,
        truncatedSixthLowerBeta,truncatedSixthLowerLambda,truncatedSixthLowerAlpha]
    linarith
  exact ⟨h,max_eq_right (by linarith)⟩

/-- On the retained domain this is literally the logarithmic kernel, not a new model parameter. -/
theorem sixth_log_retained {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    sixthLogRegular x y = log (truncatedSixthLowerS 0 x y-1)/(x*y*(1/2-x-y)) := by
  have hr : truncatedSixthLowerRegion 0 x y := by
    refine ⟨hx.1,hx.2,hy.1,hy.2.trans (moving_geometry hx).2,?_⟩
    have h := hy.2
    dsimp [lam,truncatedSixthLowerC] at h ⊢
    linarith
  have hb := truncatedSixthLower_region_bounds (by norm_num : (0:ℝ) ≤ 0) hr
  unfold sixthLogRegular
  rw [truncatedSixthMass_clip_eq hb.2.2.2,
    truncatedSixthMass_denominator_eq (by norm_num) hr]
  simp only [truncatedSixthLowerC,sub_zero]

 theorem sixth_log_nonnegative (x y : ℝ) : 0 ≤ sixthLogRegular x y := by
  unfold sixthLogRegular
  exact div_nonneg (log_nonneg (by
    have h := (truncatedSixthMass_clip_bounds (truncatedSixthLowerS 0 x y)).1
    linarith)) (truncatedSixthMass_denominator_pos 0 (x,y)).le

 theorem sixth_log_ge_exactKernel {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) : Phase25.exactKernel x y ≤ sixthLogRegular x y := by
  rw [sixth_log_retained hx hy]
  have hg := Phase25.mask_geometry hx hy
  have hs2 : 2 ≤ truncatedSixthLowerS 0 x y := by
    apply (le_div_iff₀ truncatedSixthLower_parameters.1).2
    dsimp [truncatedSixthLowerC]
    linarith [hg.2.2.2.2]
  have hl := SharpLogRecurrence.log_lower (show 1 ≤ truncatedSixthLowerS 0 x y-1 by linarith)
  have he : Phase25.exactKernel x y =
      SharpLogRecurrence.lowerLog (truncatedSixthLowerS 0 x y-1)/(x*y*(1/2-x-y)) := by
    have hz' : 1-x*2-y*2 ≠ 0 := by linarith [hg.2.2.2.1]
    simp only [Phase25.exactKernel,SharpLogRecurrence.lowerLog,truncatedSixthLowerS,truncatedSixthLowerC,lam,sub_zero]
    field_simp [truncatedSixthLower_parameters.1.ne',hg.1.ne',hg.2.1.ne',hg.2.2.2.1.ne',hz']
    ring
  rw [he]
  exact div_le_div_of_nonneg_right hl (mul_pos (mul_pos hg.1 hg.2.1) hg.2.2.2.1).le

/-- Recover the entire original log-envelope loss, rather than an isolated positive constant. -/
theorem sixth_endpoint_le_logIntegral : AnalyticTotalThreshold.sixthEndpoint ≤ sixthLogIntegral := by
  have hinner : Continuous (fun x : ℝ => ∫ y in b..s, sixthLogRegular x y) := by
    apply gamma5Gain_moving_integral (f := sixthLogRegular) sixth_log_continuous <;> fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) : Phase25.rationalInner (1/2-x) ≤
      ∫ y in b..s, sixthLogRegular x y := by
    have hc := sixth_log_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
    have hi := intervalIntegral.integral_mono_on (μ := volume) (moving_geometry hx).1
      (Phase25.inner_integrable hx) (hc.intervalIntegrable b (lam-x))
      (fun y hy => sixth_log_ge_exactKernel hx hy)
    rw [Phase25.inner_ftc hx] at hi
    have hn : 0 ≤ ∫ y in (lam-x)..s, sixthLogRegular x y :=
      intervalIntegral.integral_nonneg (moving_geometry hx).2 (fun y _hy => sixth_log_nonnegative x y)
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable b (lam-x)) (hc.intervalIntegrable (lam-x) s)
    simp only [Function.comp_apply] at hi he
    linarith [Phase25.rationalInner_lower hx]
  have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    Phase25.rationalInner_integrable (hinner.intervalIntegrable a b) hpoint
  rw [Phase25.outer_ftc] at hi
  unfold AnalyticTotalThreshold.sixthEndpoint sixthLogIntegral
  linarith

/-- Every other original signed producer and the already recovered J9 block remain unchanged. -/
def recoveredCoefficient : ℝ := AnalyticTotalThreshold.coefficient+
  JointJLossStrength.recovery/4+(sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint)/4

theorem recoveredCoefficient_le_actual : recoveredCoefficient ≤ JointHMotherPayment.unroundedCoefficient := by
  have hgap := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at hgap
  have hs := AnalyticTotalThreshold.signed_losses_nonnegative
  have hl := AnalyticTotalThreshold.losses_nonnegative
  have hj := JointJLossStrength.actual_jLoss_lower
  have h6 := sixth_recurrence_integral_cap.1
  unfold recoveredCoefficient AnalyticTotalThreshold.sixthLoss at *
  linarith only [hgap,hs.1,hs.2.1,hs.2.2.2,hl.2.1,hl.2.2.2,hj,h6]

/-- The new certificate includes the whole log-kernel recovery and is genuinely no weaker. -/
theorem recoveredCoefficient_ge_parent :
    AnalyticTotalThreshold.coefficient+JointJLossStrength.recovery/4 ≤ recoveredCoefficient := by
  unfold recoveredCoefficient
  linarith only [sixth_endpoint_le_logIntegral]

/-- A rigorous upper bound on the unpaid sixth portion after the whole log recovery. -/
theorem unpaid_sixth_quarter_cap :
    0 ≤ (truncatedSixthLowerF6lin-sixthLogIntegral)/4 ∧
      (truncatedSixthLowerF6lin-sixthLogIntegral)/4 < 1/400000 := by
  have h := sixth_recurrence_integral_cap
  constructor <;> linarith

end
end Wu2008DoubleSieve.ClassicalLossBottleneck
