import BaseGSharedActualRecovery

namespace Wu2008DoubleSieve.HighSharedKernelMagnitude
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure (a b s)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)
open BaseGSharedActualRecovery
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Interval
noncomputable section

/-- Exact primitive of the original lower envelope, not a new Taylor term. -/
def lowerPrimitive (x : ℝ) : ℝ := (8/3)*log x+8/x-4/x^2+16/(9*x^3)

theorem lowerPrimitive_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt lowerPrimitive (lowerLog (x-1)/x) x := by
  have h := ((((hasDerivAt_log hx.ne').const_mul (8/3)).add
    ((hasDerivAt_const x (8:ℝ)).div (hasDerivAt_id x) hx.ne')).sub
    ((hasDerivAt_const x (4:ℝ)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero _ hx.ne'))).add
    ((hasDerivAt_const x (16:ℝ)).div (((hasDerivAt_id x).pow 3).const_mul 9)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hx.ne')))
  convert h using 1 <;> first | rfl | (dsimp [lowerLog]; field_simp [hx.ne']; ring)

/-- The two ratios here are existing endpoint ratios; the product is exactly two. -/
theorem log_two_refined : (29712/42875:ℝ) ≤ log 2 ∧ log 2 ≤ 3566251/5145000 := by
  have h1 := log_lower (by norm_num : (1:ℝ) ≤ 4/3)
  have h2 := log_lower (by norm_num : (1:ℝ) ≤ 3/2)
  have h3 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 4/3)
  have h4 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 3/2)
  have he : log (4/3:ℝ)+log (3/2:ℝ)=log 2 := by
    rw [← log_mul (by norm_num) (by norm_num)]
    norm_num
  norm_num [JointLogTotalComparison.V,upperLog,lowerLog] at h1 h2 h3 h4
  constructor <;> linarith only [h1,h2,h3,h4,he]

theorem initial_sandwich {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    1+lowerPrimitive (v-1)-lowerPrimitive 2 ≤ wuUpperCoefficient v ∧
    wuUpperCoefficient v ≤ 1+
      (3*(upperPrimitive (v-1)-upperPrimitive 2)+
       2*(lowerPrimitive (v-1)-lowerPrimitive 2))/5 := by
  have ho : (2:ℝ) ≤ v-1 := by linarith
  have hiL : IntervalIntegrable (fun x => lowerLog (x-1)/x) volume 2 (v-1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · unfold lowerLog
      have hn : ∀ x ∈ uIcc (2:ℝ) (v-1), x-1+1 ≠ 0 := by
        intro x hx; rw [uIcc_of_le ho] at hx; linarith [hx.1]
      fun_prop (disch := assumption)
    · exact continuousOn_id
    · intro x hx; rw [uIcc_of_le ho] at hx; linarith [hx.1]
  have hiU : IntervalIntegrable (fun x => upperLog (x-1)/x) volume 2 (v-1) := by
    apply ContinuousOn.intervalIntegrable

    apply ContinuousOn.div
    · unfold upperLog
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro x hx; rw [uIcc_of_le ho] at hx
      have : 0 < x-1 := by linarith [hx.1]
      have : 0 < x-1+1 := by linarith [hx.1]
      positivity
    · exact continuousOn_id
    · intro x hx; rw [uIcc_of_le ho] at hx; linarith [hx.1]
  have hi := wuLowerCoefficient_div_intervalIntegrable (by norm_num : (0:ℝ)<2) ho
  have eL := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => lowerPrimitive_derivative (by rw [uIcc_of_le ho] at hx; linarith [hx.1])) hiL
  have eU := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => upperPrimitive_derivative (by rw [uIcc_of_le ho] at hx; exact hx.1)) hiU
  have hl := intervalIntegral.integral_mono_on ho hiL hi (fun x hx => by
    rw [show wuLowerCoefficient x = log (x-1) from
      jr1965f_normalized_firstInterval hx.1 (by linarith [hx.2])]
    exact div_le_div_of_nonneg_right (log_lower (by linarith [hx.1])) (by linarith [hx.1]))
  have hu := intervalIntegral.integral_mono_on ho hi
    (((hiU.const_mul 3).add (hiL.const_mul 2)).div_const 5) (fun x hx => by
      rw [show wuLowerCoefficient x = log (x-1) from
        jr1965f_normalized_firstInterval hx.1 (by linarith [hx.2])]
      have h := div_le_div_of_nonneg_right
        (JointLogTotalComparison.log_le_V (show 1 ≤ x-1 by linarith [hx.1]))
        (show 0 ≤ x by linarith [hx.1])
      convert h using 1 <;> first | rfl | (unfold JointLogTotalComparison.V; ring))
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2:ℝ)≤3) hv
  have hinit : wuUpperCoefficient 3=1 := jr1965F_normalized_initial (by norm_num) le_rfl
  norm_num only [show (3:ℝ)-1=2 by norm_num,hinit] at hr
  rw [eL] at hl
  simp_rw [show ∀ z : ℝ, z/5=z*(5:ℝ)⁻¹ from fun z => div_eq_mul_inv z 5] at hu
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add (hiU.const_mul 3) (hiL.const_mul 2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,eL,eU] at hu
  constructor <;> linarith only [hl,hu,hr]

theorem upper_five_sandwich :
    (541588/385875:ℝ) ≤ wuUpperCoefficient 5 ∧
    wuUpperCoefficient 5 ≤ 9044059/6431250 := by
  have h := initial_sandwich (by norm_num : (3:ℝ)≤5) le_rfl
  have h2 := log_two_refined
  have h32 := log_lower (by norm_num : (1:ℝ)≤3/2)
  have h3 : (29712/42875:ℝ)+lowerLog (3/2) ≤ log 3 := by
    have he : log 3=log 2+log (3/2:ℝ) := by
      rw [← log_mul (by norm_num) (by norm_num)]; norm_num
    rw [he]; linarith only [h2.1,h32]
  have he : log (4:ℝ)=2*log 2 := by
    have h := log_pow (2:ℝ) 2
    norm_num at h
    exact h
  norm_num [lowerPrimitive,upperPrimitive,he,lowerLog] at h h3
  constructor <;> linarith only [h.1,h.2,h2.1,h2.2,h3]

/-- Actual delayed lower density, with no continuation of the initial log formula. -/
theorem lower_ratio_four {x : ℝ} (hx : 4 ≤ x) : log 3/4 ≤ wuLowerCoefficient x/x := by
  have hf := monotoneOn_jr1965f (by norm_num : (4:ℝ) ∈ Ioi 0)
    (show x ∈ Ioi 0 by change 0 < x; linarith) hx
  have he : 0 < 2*exp eulerMascheroniConstant := by positivity
  have h := div_le_div_of_nonneg_right hf he.le
  have h4 := BaseRecurrenceLower.lower_four_value
  have hx0 : x ≠ 0 := by linarith
  have hx4 : wuLowerCoefficient x/x = jr1965f x/(2*exp eulerMascheroniConstant) := by
    unfold wuLowerCoefficient; field_simp
  rw [hx4]
  have h44 : wuLowerCoefficient 4/4 = jr1965f 4/(2*exp eulerMascheroniConstant) := by
    unfold wuLowerCoefficient; ring
  rw [← h44,h4] at h
  exact h

/-- A whole-window recurrence lower bound, including its genuine delayed tail. -/
theorem upper_high_lower {v : ℝ} (hv : 5 ≤ v) :
    wuUpperCoefficient 5+(log 3/4)*(v-5) ≤ wuUpperCoefficient v := by
  have ho : (4:ℝ) ≤ v-1 := by linarith
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2:ℝ)≤5) hv
  have hm := intervalIntegral.integral_mono_on ho (intervalIntegrable_const)
    (wuLowerCoefficient_div_intervalIntegrable (by norm_num) ho)
    (fun x hx => lower_ratio_four hx.1)
  norm_num only [show (5:ℝ)-1=4 by norm_num] at hr
  rw [intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  linarith only [hr,hm]

/-- Explicit rational bilateral comparison on the entire original high window. -/
theorem high_pointwise {v : ℝ} (hv : 5 ≤ v) (_hvc : v ≤ 1127/200) :
    (1845671/520931250:ℝ) ≤ (42823/151875)*v-wuUpperCoefficient v ∧
    (42823/151875)*v-wuUpperCoefficient v ≤
      65413/10418625+(1183/151875)*(v-5) := by
  have h5 := upper_five_sandwich
  have ha := SharpSingleBalance.upper_ratio_antitone (by norm_num : (0:ℝ)<5) hv
  have hv0 : 0 < v := by linarith
  have ha' := (div_le_iff₀ hv0).1 (ha.trans (div_le_div_of_nonneg_right h5.2 (by norm_num)))
  have hl := upper_high_lower hv
  have h3 := log_three_bounds.1
  have hp := mul_le_mul_of_nonneg_right h3 (show 0 ≤ (v-5)/4 by positivity)
  constructor
  · nlinarith only [ha',hv]
  · linarith only [hl,h5.1,hp]

/-- No new cut: all geometry is on the original high interval. -/
theorem high_geometry {t : ℝ} (ht : t ∈ Icc a (c 5)) :
    0 < t ∧ 0 < 1/2-t ∧ 5 ≤ u t ∧ u t ≤ 1127/200 := by
  have ha := truncatedSixthLower_parameters.1
  have ht0 := ha.trans_le ht.1
  have hd : 0 < 1/2-t := by norm_num [c,a,truncatedSixthLowerAlpha] at ht; linarith
  refine ⟨ht0,hd,?_,?_⟩
  · apply (le_div_iff₀ ha).2
    have h : t ≤ 1/2-5*a := ht.2
    linarith
  · apply (div_le_iff₀ ha).2
    norm_num [a,truncatedSixthLowerAlpha] at ht ⊢
    linarith only [ht.1]

theorem high_weight {t : ℝ} (ht : t ∈ Icc a (c 5)) :
    (100:ℝ) ≤ SharedRationalEnvelope.weight t ∧ SharedRationalEnvelope.weight t ≤ 200 := by
  have hg := high_geometry ht
  have hd := mul_pos hg.1 hg.2.1
  unfold SharedRationalEnvelope.weight
  constructor
  · apply (le_div_iff₀ hd).2
    have hp := mul_nonneg (show 0 ≤ c 5-t by linarith [ht.2])
      (show 0 ≤ 74-100*(t+c 5) by norm_num [c,a,truncatedSixthLowerAlpha] at ht ⊢; linarith)
    norm_num [c,a,truncatedSixthLowerAlpha] at hp
    nlinarith only [hp]
  · apply (div_le_iff₀ hd).2
    have hp := mul_nonneg (show 0 ≤ t-a by linarith [ht.1])
      (show 0 ≤ 124-200*(t+a) by norm_num [c,a,truncatedSixthLowerAlpha] at ht ⊢; linarith)
    norm_num [a,truncatedSixthLowerAlpha] at hp
    nlinarith only [hp]

/-- The actual kernel density has its original signed net weight. -/
theorem kernel_density (p : ℝ → ℝ) (t : ℝ) :
    (8-24*t)*(p (u t)/(t*(1/2-t))-ClassicalSingleBounds.g t) =
      SharedRationalEnvelope.weight t*(p (u t)-wuUpperCoefficient (u t)) := by
  dsimp [SharedRationalEnvelope.weight,ClassicalSingleBounds.g,ClassicalSingleBounds.a,u,a]
  ring

/-- Exact FTC of the affine recurrence bound after the original change of variables. -/
def highCapDensity (t : ℝ) : ℝ :=
  200*(65413/10418625+(1183/151875)*(c 5-t)/a)
def highCapPrimitive (t : ℝ) : ℝ :=
  200*((65413/10418625)*t+(1183/151875)*(c 5*t-t^2/2)/a)

theorem highCap_derivative (t : ℝ) : HasDerivAt highCapPrimitive (highCapDensity t) t := by
  convert ((((hasDerivAt_id t).const_mul (65413/10418625)).add
    ((((hasDerivAt_id t).const_mul (c 5)).sub (((hasDerivAt_id t).pow 2).div_const 2)).const_mul
      (1183/151875) |>.div_const a)).const_mul 200) using 1 <;>
    first | rfl | (dsimp [highCapDensity]; ring)

/-- A true bilateral magnitude for the whole original high kernel. -/
theorem high_bounds : (1/60:ℝ) < highKernel ∧ highKernel < 1/10 := by
  have ho : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hs : c 5 ≤ s := by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hi := kernel_integrable (fun v => (42823/151875)*v) le_rfl hs ho (by fun_prop)
  have hl := intervalIntegral.integral_mono_on ho
    (intervalIntegrable_const (c := (100:ℝ)*(1845671/520931250))) hi (fun t ht => ?_)
  · have hc : Continuous highCapDensity := by unfold highCapDensity; fun_prop
    have hu := intervalIntegral.integral_mono_on ho hi (hc.intervalIntegrable _ _) (fun t ht => ?_)
    · rw [intervalIntegral.integral_const] at hl
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => highCap_derivative t)
        (hc.intervalIntegrable _ _)] at hu
      change _ ≤ highKernel at hl
      change highKernel ≤ _ at hu
      norm_num [highCapPrimitive,a,c,truncatedSixthLowerAlpha,smul_eq_mul] at hl hu
      constructor <;> linarith only [hl,hu]
    have hg := high_geometry ht
    have hb := high_pointwise hg.2.2.1 hg.2.2.2
    have hw := high_weight ht
    rw [kernel_density]
    have hn : 0 ≤ (42823/151875)*u t-wuUpperCoefficient (u t) := by linarith only [hb.1]
    have he : u t-5=(c 5-t)/a := by unfold u c; field_simp [truncatedSixthLower_parameters.1.ne']; ring
    have hm := mul_le_mul hw.2 hb.2 hn (by norm_num : (0:ℝ)≤200)
    rw [he] at hm
    convert hm using 1 <;> first | rfl | (unfold highCapDensity; ring)
  have hg := high_geometry ht
  have hb := high_pointwise hg.2.2.1 hg.2.2.2
  have hw := high_weight ht
  rw [kernel_density]
  exact mul_le_mul hw.1 hb.1 (by norm_num : (0:ℝ)≤1845671/520931250) (by linarith only [hw.1])

theorem middle_pointwise {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    GConvexChord.C+GConvexChord.m*v-wuUpperCoefficient v ≤
      (65413/10418625)+(11/40-GConvexChord.m) := by
  have ho : v-1 ≤ (4:ℝ) := by linarith [hv.2]
  have hr := wuUpperCoefficient_sub_eq_integral (show 2 ≤ v by linarith [hv.1]) hv.2
  have hm := intervalIntegral.integral_mono_on ho
    (wuLowerCoefficient_div_intervalIntegrable (show 0 < v-1 by linarith [hv.1]) ho)
    (intervalIntegrable_const (c := (11/40:ℝ))) (fun x hx => by
      rw [show wuLowerCoefficient x=log (x-1) from
        jr1965f_normalized_firstInterval (by linarith [hx.1,hv.1]) hx.2]
      have h := GConvexChord.density_monotone
        (show x+1 ∈ Icc (4:ℝ) 5 by constructor <;> linarith [hx.1,hx.2,hv.1])
        (by norm_num : (5:ℝ) ∈ Icc (4:ℝ) 5) (by linarith [hx.2])
      have he : GConvexChord.density (x+1)=log (x-1)/x := by
        unfold GConvexChord.density; congr 2 <;> ring
      rw [he] at h
      norm_num [GConvexChord.density] at h
      linarith only [h,log_three_bounds.2])
  norm_num only [show (5:ℝ)-1=4 by norm_num] at hr
  rw [intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  have h5 := upper_five_sandwich.1
  norm_num [GConvexChord.C,GConvexChord.m,GConvexChord.r4,GConvexChord.r5] at *
  linarith only [hr,hm,h5,hv.1]

/-- Uniform bounds are proved from the original quadratic denominator, not sampled. -/
theorem middle_weight {t : ℝ} (ht : t ∈ Icc (c 5) (c 4)) :
    0 ≤ SharedRationalEnvelope.weight t ∧ SharedRationalEnvelope.weight t ≤ 110 := by
  have ht0 : 0 < t := by norm_num [c,a,truncatedSixthLowerAlpha] at ht; linarith
  have hd : 0 < 1/2-t := by norm_num [c,a,truncatedSixthLowerAlpha] at ht; linarith
  have hn : 0 ≤ 8-24*t := by norm_num [c,a,truncatedSixthLowerAlpha] at ht; linarith
  unfold SharedRationalEnvelope.weight
  refine ⟨div_nonneg hn (mul_pos ht0 hd).le,?_⟩
  apply (div_le_iff₀ (mul_pos ht0 hd)).2
  have hp := mul_nonneg (show 0 ≤ t-c 5 by linarith [ht.1])
    (show 0 ≤ 79-110*(t+c 5) by norm_num [c,a,truncatedSixthLowerAlpha] at ht ⊢; linarith)
  norm_num [a,c,truncatedSixthLowerAlpha] at hp
  nlinarith only [hp]

theorem middle_bound : middleKernel < (1/5:ℝ) := by
  have ho : c 5 ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hi := kernel_integrable (fun v => GConvexChord.C+GConvexChord.m*v)
    (by norm_num [a,c,truncatedSixthLowerAlpha])
    (by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]) ho (by fun_prop)
  have hm := intervalIntegral.integral_mono_on ho hi
    (intervalIntegrable_const (c := (110:ℝ)*(65413/10418625+(11/40-GConvexChord.m))))
    (fun t ht => ?_)
  · rw [intervalIntegral.integral_const] at hm
    change middleKernel ≤ _ at hm
    norm_num [smul_eq_mul,c,a,truncatedSixthLowerAlpha,GConvexChord.m,GConvexChord.r4,GConvexChord.r5] at hm
    linarith only [hm]
  have ha := truncatedSixthLower_parameters.1
  have hv : u t ∈ Icc (4:ℝ) 5 := by
    constructor
    · apply (le_div_iff₀ ha).2
      have h : t ≤ 1/2-4*a := ht.2
      linarith
    · apply (div_le_iff₀ ha).2
      have h : 1/2-5*a ≤ t := ht.1
      linarith
  have hp := middle_pointwise hv
  have hw := middle_weight ht
  rw [kernel_density (fun v => GConvexChord.C+GConvexChord.m*v)]
  have hcap : 0 ≤ (65413/10418625:ℝ)+(11/40-GConvexChord.m) := by
    norm_num [GConvexChord.m,GConvexChord.r4,GConvexChord.r5]
  exact (mul_le_mul_of_nonneg_left hp hw.1).trans (mul_le_mul_of_nonneg_right hw.2 hcap)

theorem low_weight {t : ℝ} (ht : t ∈ Icc (c 4) s) :
    0 ≤ SharedRationalEnvelope.weight t ∧ SharedRationalEnvelope.weight t ≤ 55 := by
  have hg := SharedRationalEnvelope.geometry ht
  have hd := mul_pos hg.1 hg.2.1
  have hn : 0 ≤ 8-24*t := by norm_num [s,truncatedSixthLowerSigma,truncatedSixthLowerAlpha] at ht; linarith [ht.2]
  unfold SharedRationalEnvelope.weight
  refine ⟨div_nonneg hn hd.le,?_⟩
  apply (div_le_iff₀ hd).2
  have hp := mul_nonneg (show 0 ≤ t-c 4 by linarith [ht.1])
    (show 0 ≤ 103/2-55*(t+c 4) by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma] at ht ⊢; linarith)
  norm_num [a,c,truncatedSixthLowerAlpha] at hp
  nlinarith only [hp]

/-- The exact difference of the two already existing polynomial envelopes. -/
def lowCapDensity (t : ℝ) : ℝ := 55*((5/36)*(u t-3)^2-(u t-3)^3/12)
def lowCapPrimitive (t : ℝ) : ℝ := -55*a*((5/108)*(u t-3)^3-(u t-3)^4/48)

theorem lowCap_derivative (t : ℝ) : HasDerivAt lowCapPrimitive (lowCapDensity t) t := by
  have hd := (((hasDerivAt_const t (1/2:ℝ)).sub (hasDerivAt_id t)).div_const a).sub_const 3
  convert ((((hd.pow 3).const_mul (5/108)).sub ((hd.pow 4).div_const 48)).const_mul (-55*a)) using 1 <;>
    first | rfl | (dsimp [lowCapDensity,u]; field_simp [truncatedSixthLower_parameters.1.ne']; ring)

theorem low_bound : lowKernel < (1/9:ℝ) := by
  have ho := SharedRationalEnvelope.window_order.2.1
  have hi := kernel_integrable VariableUpperEnvelope.cubic
    SharedRationalEnvelope.window_order.1 le_rfl ho (by unfold VariableUpperEnvelope.cubic; fun_prop)
  have hc : Continuous lowCapDensity := by unfold lowCapDensity u; fun_prop
  have hm := intervalIntegral.integral_mono_on ho hi (hc.intervalIntegrable _ _) (fun t ht => ?_)
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => lowCap_derivative t) (hc.intervalIntegrable _ _)] at hm
    have hdelta := SharedRationalEnvelope.deltaShared_pos
    change kernel VariableUpperEnvelope.cubic (c 4) s ≤ _ at hm
    unfold lowKernel
    norm_num [lowCapPrimitive,u,s,c,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma] at hm ⊢
    linarith only [hm,hdelta]
  have hg := SharedRationalEnvelope.geometry ht
  have hu := SharpSingleBalance.upper_quadratic hg.2.2.1 hg.2.2.2
  have hw := low_weight ht
  have hp : VariableUpperEnvelope.cubic (u t)-wuUpperCoefficient (u t) ≤
      (5/36)*(u t-3)^2-(u t-3)^3/12 := by
    unfold VariableUpperEnvelope.cubic
    linarith only [hu]
  have hz : 0 ≤ u t-3 ∧ u t-3 ≤ 1 := by constructor <;> linarith [hg.2.2.1,hg.2.2.2]
  have hn : 0 ≤ (5/36)*(u t-3)^2-(u t-3)^3/12 := by
    have h := mul_nonneg (sq_nonneg (u t-3)) (show 0 ≤ 5/36-(u t-3)/12 by linarith [hz.2])
    nlinarith only [h]
  rw [kernel_density]
  exact (mul_le_mul_of_nonneg_left hp hw.1).trans (mul_le_mul_of_nonneg_right hw.2 hn)

theorem beta_bound : betaKernel ≤ (1/12500:ℝ) := by
  have ho : (3:ℝ) ≤ 78/25 := by norm_num
  have hu := wuUpperCoefficient_div_intervalIntegrable (by norm_num : (0:ℝ)<3) ho
  have hq := BaseRecurrenceLower.polynomial_div_integrable
    (fun v : ℝ => 1+(v-3)^2/9) (by fun_prop) (by norm_num) ho
  have hi : IntervalIntegrable (fun v : ℝ => (wuUpperCoefficient v-(1+(v-3)^2/9))/v)
      volume 3 (78/25) := by simpa only [sub_div] using hu.sub hq
  have hm := intervalIntegral.integral_mono_on ho hi
    (intervalIntegrable_const (c := (1/1500:ℝ))) (fun v hv => by
      have hv0 : 0 < v := by linarith [hv.1]
      have h := VariableUpperEnvelope.upper_cubic hv.1 (show v ≤ 4 by linarith [hv.2])
      have hz : 0 ≤ v-3 ∧ v-3 ≤ 3/25 := by constructor <;> linarith [hv.1,hv.2]
      have hs : (v-3)^2 ≤ (3/25:ℝ)^2 := sq_le_sq₀ hz.1 (by norm_num) |>.2 hz.2
      have hc : 0 ≤ (v-3)^3 := pow_nonneg hz.1 _
      apply (div_le_iff₀ hv0).2
      unfold VariableUpperEnvelope.cubic at h
      nlinarith only [h,hs,hc,hv.1])
  rw [intervalIntegral.integral_const] at hm
  change betaKernel ≤ _ at hm
  norm_num [smul_eq_mul] at hm
  exact hm

theorem base_bound : AnalyticTotalThreshold.baseLoss < (1/100:ℝ) := by
  have h1 := log_upper (by norm_num : (1:ℝ)≤3/2)
  have h2 := log_upper (by norm_num : (1:ℝ)≤26/25)
  have hb := beta_bound
  rw [base_exact]
  unfold baseLogRemainder
  norm_num [upperLog,lowerLog] at h1 h2 ⊢
  linarith only [h1,h2,hb]

theorem g_bound : AnalyticTotalThreshold.gLoss < (1/20:ℝ) := by
  have h1 := log_lower (show 1 ≤ c 5/a by norm_num [c,a,truncatedSixthLowerAlpha])
  have h2 := log_lower (show 1 ≤ c 4/c 5 by norm_num [c,a,truncatedSixthLowerAlpha])
  have h3 := log_lower (show 1 ≤ s/c 4 by norm_num [s,c,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h4 := log_lower (show 1 ≤ 6*a/s by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  rw [g_exact]
  unfold gLogRemainder
  norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma,GConvexChord.C,GConvexChord.m,
    GConvexChord.r4,GConvexChord.r5,VariableGIntegral.logCoefficient,VariableGIntegral.a,
    upperLog,lowerLog] at h1 h2 h3 h4 ⊢
  linarith only [h1,h2,h3,h4]

/-- Retain the variable net weight in the lower comparison as well. -/
def highRecovery : ℝ := (1845671/520931250)/(5*a)*(8*lowerLog (c 5/a)-24*(c 5-a))
def highLowerDensity (t : ℝ) : ℝ := (1845671/520931250)/(5*a)*(8/t-24)
def highLowerPrimitive (t : ℝ) : ℝ := (1845671/520931250)/(5*a)*(8*log t-24*t)

theorem highLower_derivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt highLowerPrimitive (highLowerDensity t) t := by
  convert (((hasDerivAt_log ht.ne').const_mul 8).sub ((hasDerivAt_id t).const_mul 24)).const_mul
    ((1845671/520931250)/(5*a)) using 1 <;> first | rfl | (dsimp [highLowerDensity]; ring)

theorem high_recovery : highRecovery ≤ highKernel := by
  have ho : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hs : c 5 ≤ s := by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hi := kernel_integrable (fun v => (42823/151875)*v) le_rfl hs ho (by fun_prop)
  have hL : IntervalIntegrable highLowerDensity volume a (c 5) := by
    apply ContinuousOn.intervalIntegrable
    unfold highLowerDensity
    apply continuousOn_const.mul
    apply ContinuousOn.sub _ continuousOn_const
    apply continuousOn_const.div continuousOn_id
    intro t ht
    rw [uIcc_of_le ho] at ht
    exact (high_geometry ht).1.ne'
  have hm := intervalIntegral.integral_mono_on ho hL hi (fun t ht => ?_)
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => highLower_derivative (high_geometry (uIcc_of_le ho ▸ ht)).1) hL] at hm
    change highLowerPrimitive (c 5)-highLowerPrimitive a ≤ highKernel at hm
    have hh := log_lower (show 1 ≤ c 5/a by norm_num [a,c,truncatedSixthLowerAlpha])
    rw [log_div (truncatedSixthLower_parameters.1.trans_le ho).ne'
      truncatedSixthLower_parameters.1.ne'] at hh
    unfold highRecovery
    unfold highLowerPrimitive at hm
    norm_num [a,c,truncatedSixthLowerAlpha,lowerLog] at hh hm ⊢
    linarith only [hh,hm]
  have hg := high_geometry ht
  have ha := SharpSingleBalance.upper_ratio_antitone (by norm_num : (0:ℝ)<5) hg.2.2.1
  have h5 := upper_five_sandwich.2
  have hv0 : 0 < u t := by linarith only [hg.2.2.1]
  have ha' := (div_le_iff₀ hv0).1 (ha.trans (div_le_div_of_nonneg_right h5 (by norm_num)))
  have hb : (1845671/520931250:ℝ)*u t/5 ≤ (42823/151875)*u t-wuUpperCoefficient (u t) := by
    linarith only [ha']
  have hw : 0 ≤ SharedRationalEnvelope.weight t := by linarith only [(high_weight ht).1]
  rw [kernel_density]
  have hp := mul_le_mul_of_nonneg_left hb hw
  calc
    highLowerDensity t = SharedRationalEnvelope.weight t*((1845671/520931250)*u t/5) := by
      unfold highLowerDensity SharedRationalEnvelope.weight u
      have hn : 1-t*2 ≠ 0 := by linarith [hg.2.1]
      field_simp [truncatedSixthLower_parameters.1.ne',hg.1.ne',hg.2.1.ne',hn]
    _ ≤ _ := hp

theorem high_recovery_exact : highRecovery =
    (747947812051847777/28591933452813281250:ℝ) := by
  norm_num [highRecovery,a,c,truncatedSixthLowerAlpha,lowerLog]

theorem high_magnitude : (1/40:ℝ) < highKernel ∧ highKernel < 1/10 := by
  have h := high_recovery
  rw [high_recovery_exact] at h
  exact ⟨by linarith only [h],high_bounds.2⟩

/-- Full high-window difference with its actual iterated-log continuation retained. -/
theorem high_delay_exact {v : ℝ} (hv : 5 ≤ v) (hvc : v ≤ 1127/200) :
    (42823/151875)*v-explicitUpper v =
      (42823/30375-wuUpperCoefficient 5)+(42823/151875)*(v-5)-
        ∫ x in (4:ℝ)..(v-1), (log (x-1)+lowerLogKernel x)/x := by
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2:ℝ)≤5) hv
  have ho : (4:ℝ)≤v-1 := by linarith
  have he : (∫ x in (4:ℝ)..(v-1), wuLowerCoefficient x/x) =
      ∫ x in (4:ℝ)..(v-1), (log (x-1)+lowerLogKernel x)/x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ho] at hx
    dsimp only
    rw [lower_log_kernel_exact hx.1 (by linarith [hx.2])]
  norm_num only [show (5:ℝ)-1=4 by norm_num] at hr
  rw [he,upper_explicit_exact (by linarith) hvc] at hr
  linarith only [hr]

theorem explicit_high_comparison {v : ℝ} (hv : 5 ≤ v) (hvc : v ≤ 1127/200) :
    (1845671/520931250:ℝ) ≤ (42823/151875)*v-explicitUpper v ∧
    (42823/151875)*v-explicitUpper v ≤ 65413/10418625+(1183/151875)*(v-5) := by
  rw [← upper_explicit_exact (by linarith) hvc]
  exact high_pointwise hv hvc

/-- Literal complete B/G/shared quantity, with a genuine upper bound as well as a lower bound. -/
theorem triple_bounds :
    (3/100:ℝ) < AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+AnalyticTotalThreshold.sharedLoss ∧
    AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+AnalyticTotalThreshold.sharedLoss < 1/2 := by
  have hn := AnalyticTotalThreshold.signed_losses_nonnegative
  have hh := high_magnitude
  have hm := middle_recovery
  have hl := low_nonnegative
  rw [recovery_exact] at hm
  rw [shared_exact]
  constructor
  · linarith only [hn.1,hn.2.1,hh.1,hm,hl]
  · linarith only [base_bound,g_bound,hh.2,middle_bound,low_bound]

/-- Spend only the newly quantified high payment on top of the parent middle payment. -/
def coefficient : ℝ := BaseGSharedActualRecovery.coefficient+highRecovery/4

theorem coefficient_le_actual : coefficient ≤ JointHMotherPayment.unroundedCoefficient := by
  have he := BaseGSharedActualRecovery.seven_error_exact
  have hb := AnalyticTotalThreshold.signed_losses_nonnegative
  have hl := AnalyticTotalThreshold.losses_nonnegative
  have hj := JointJLossStrength.actual_jLoss_lower
  have h6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.1
  have h4 := FourActualCapRecovery.actual_fourLoss_lower
  have hh := high_recovery
  have hm := middle_recovery
  have hlo := low_nonnegative
  rw [unpaid_triple_exact,shared_exact] at he
  unfold coefficient AnalyticTotalThreshold.sixthLoss at *
  linarith only [he,hb.1,hb.2.1,hl.2.1,hj,h6,h4,hh,hm,hlo]

/-- The complete three-loss certificate is located relative to the old diagnostic, not mistaken for Q. -/
def fullTripleCoefficient : ℝ := JointSixthFourDiagnostic.coefficient+
  (AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+AnalyticTotalThreshold.sharedLoss)/4

theorem full_triple_gain_bounds :
    (3/400:ℝ) < fullTripleCoefficient-JointSixthFourDiagnostic.coefficient ∧
    fullTripleCoefficient-JointSixthFourDiagnostic.coefficient < 1/8 := by
  have h := triple_bounds
  unfold fullTripleCoefficient
  constructor <;> linarith only [h.1,h.2]

theorem full_triple_coefficient_le_actual : fullTripleCoefficient ≤ JointHMotherPayment.unroundedCoefficient := by
  have hgap := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at hgap
  have hl := AnalyticTotalThreshold.losses_nonnegative
  have hj := JointJLossStrength.actual_jLoss_lower
  have h6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.1
  have h4 := FourActualCapRecovery.actual_fourLoss_lower
  unfold fullTripleCoefficient JointSixthFourDiagnostic.coefficient ClassicalLossBottleneck.recoveredCoefficient
  unfold AnalyticTotalThreshold.sixthLoss at hgap h6
  linarith only [hgap,hl.2.1,hj,h6,h4]

end
end Wu2008DoubleSieve.HighSharedKernelMagnitude
