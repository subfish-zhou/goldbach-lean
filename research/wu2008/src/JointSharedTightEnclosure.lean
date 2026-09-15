import HighSharedKernelMagnitude
import FifthLogTotalMagnitude

namespace Wu2008DoubleSieve.JointSharedTightEnclosure
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure (a b s)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)
open BaseGSharedActualRecovery
open HighSharedKernelMagnitude (initial_sandwich lowerPrimitive log_two_refined)
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Interval
noncomputable section

theorem four_sandwich : (34832/30375:ℝ) ≤ wuUpperCoefficient 4 ∧
    wuUpperCoefficient 4 ≤ 287/250 := by
  have h := initial_sandwich (by norm_num : (3:ℝ)≤4) (by norm_num)
  have hl := log_lower (by norm_num : (1:ℝ)≤3/2)
  have hu := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ)≤3/2)
  have h2 := log_two_refined
  have he : log (3:ℝ)=log 2+log (3/2:ℝ) := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  norm_num [lowerPrimitive,upperPrimitive,he,lowerLog,JointLogTotalComparison.V,upperLog] at h hl hu
  constructor <;> linarith only [h.1,h.2,hl,hu,h2.1,h2.2]

/-- Upper curvature from the original density derivative on the original whole window. -/
theorem curvature_upper {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    (1+1/(v-2)-log (v-2))/(v-1)^2 ≤ 1/11 := by
  have h2 : 0 < v-2 := by linarith [hv.1]
  have hi : 1/(v-2) ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ h2).2; linarith [hv.1]
  have hl := log_le_log (by norm_num : (0:ℝ)<2) (show 2 ≤ v-2 by linarith [hv.1])
  have hs : (9:ℝ) ≤ (v-1)^2 := by nlinarith [hv.1]
  apply (div_le_iff₀ (sq_pos_of_pos (show 0 < v-1 by linarith [hv.1]))).2
  linarith only [hi,hl,hs,log_two_refined.1]

def reverseUpper (v : ℝ) : ℝ := v^2/22-wuUpperCoefficient v
def reverseDensity (v : ℝ) : ℝ := v/11-GConvexChord.density v

theorem reverse_upper_derivative {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    HasDerivAt reverseUpper (reverseDensity v) v := by
  convert (((hasDerivAt_id v).pow 2).div_const 22).sub (GConvexChord.upper_derivative hv) using 1 <;>
    first | rfl | (dsimp [reverseDensity]; ring)

theorem reverse_density_derivative {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    HasDerivAt reverseDensity (1/11-(1+1/(v-2)-log (v-2))/(v-1)^2) v := by
  exact ((hasDerivAt_id v).div_const 11).sub (GConvexChord.density_derivative hv)

theorem reverse_density_monotone : MonotoneOn reverseDensity (Icc (4:ℝ) 5) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro v hv; exact (reverse_density_derivative hv).continuousAt.continuousWithinAt
  · intro v hv; exact (reverse_density_derivative (interior_subset hv)).differentiableAt.differentiableWithinAt
  · intro v hv
    rw [(reverse_density_derivative (interior_subset hv)).deriv]
    exact sub_nonneg.mpr (curvature_upper (interior_subset hv))

theorem reverse_upper_convex : ConvexOn ℝ (Icc (4:ℝ) 5) reverseUpper := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _)
  · intro v hv; exact (reverse_upper_derivative hv).continuousAt.continuousWithinAt
  · intro v hv; exact (reverse_upper_derivative (interior_subset hv)).differentiableAt.differentiableWithinAt
  · intro v hv w hw hvw
    rw [(reverse_upper_derivative (interior_subset hv)).deriv,
      (reverse_upper_derivative (interior_subset hw)).deriv]
    exact reverse_density_monotone (interior_subset hv) (interior_subset hw) hvw

/-- Real endpoint chord errors, before any rational endpoint relaxation. -/
theorem true_chord_sandwich {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    (v-4)*(5-v)/144 ≤ (5-v)*wuUpperCoefficient 4+(v-4)*wuUpperCoefficient 5-wuUpperCoefficient v ∧
    (5-v)*wuUpperCoefficient 4+(v-4)*wuUpperCoefficient 5-wuUpperCoefficient v ≤ (v-4)*(5-v)/22 := by
  have hl := GCurvatureChord.corrected_upper_convex.2
    (by norm_num : (4:ℝ) ∈ Icc (4:ℝ) 5) (by norm_num : (5:ℝ) ∈ Icc (4:ℝ) 5)
    (show 0 ≤ 5-v by linarith [hv.2]) (show 0 ≤ v-4 by linarith [hv.1])
    (show (5-v)+(v-4)=1 by ring)
  have hu := reverse_upper_convex.2
    (by norm_num : (4:ℝ) ∈ Icc (4:ℝ) 5) (by norm_num : (5:ℝ) ∈ Icc (4:ℝ) 5)
    (show 0 ≤ 5-v by linarith [hv.2]) (show 0 ≤ v-4 by linarith [hv.1])
    (show (5-v)+(v-4)=1 by ring)
  simp only [smul_eq_mul,show (5-v)*4+(v-4)*5=v by ring] at hl hu
  dsimp [GCurvatureChord.correctedUpper,reverseUpper] at hl hu
  constructor <;> nlinarith only [hl,hu]

def middleLo (v : ℝ) : ℝ :=
  (5-v)*(GConvexChord.r4-287/250)+(v-4)*(GConvexChord.r5-9044059/6431250)+(v-4)*(5-v)/144
def middleHi (v : ℝ) : ℝ :=
  (5-v)*(GConvexChord.r4-34832/30375)+(v-4)*(GConvexChord.r5-541588/385875)+(v-4)*(5-v)/22

theorem middle_pointwise {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    middleLo v ≤ GConvexChord.C+GConvexChord.m*v-wuUpperCoefficient v ∧
    GConvexChord.C+GConvexChord.m*v-wuUpperCoefficient v ≤ middleHi v := by
  have hc := true_chord_sandwich hv
  have h4 := four_sandwich
  have h5 := HighSharedKernelMagnitude.upper_five_sandwich
  have h4l := mul_le_mul_of_nonneg_left h4.1 (show 0 ≤ 5-v by linarith [hv.2])
  have h4u := mul_le_mul_of_nonneg_left h4.2 (show 0 ≤ 5-v by linarith [hv.2])
  have h5l := mul_le_mul_of_nonneg_left h5.1 (show 0 ≤ v-4 by linarith [hv.1])
  have h5u := mul_le_mul_of_nonneg_left h5.2 (show 0 ≤ v-4 by linarith [hv.1])
  dsimp [middleLo,middleHi,GConvexChord.C,GConvexChord.m] at *
  constructor <;> nlinarith only [hc.1,hc.2,h4l,h4u,h5l,h5u]

/-- Direct derivative error of p-U, not cubic-U and not a new logarithmic order. -/
theorem p_derivative {v : ℝ} (hv : 3 ≤ v) :
    HasDerivAt SharedRationalEnvelope.p
      (1/2-2/(v-1)^2-2*(v-3)^2/(v-1)^4) v := by
  have hn : v-1 ≠ 0 := by linarith
  have hd := (((hasDerivAt_id v).sub_const 3).div ((hasDerivAt_id v).sub_const 1) hn)
  have hh := (((hasDerivAt_id v).sub_const 1).sub
    ((hd.const_mul 2).add ((hd.pow 3).const_mul (2/3)))).div_const 2
  convert! hh using 1
  · funext x
    dsimp [SharedRationalEnvelope.p,lowerLog]
    rw [show x-2-1=x-3 by ring,show x-2+1=x-1 by ring]
    ring
  · dsimp; field_simp [hn]; ring

theorem initial_derivative {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    HasDerivAt wuUpperCoefficient (log (v-2)/(v-1)) v := by
  have h := (hasDerivAt_mul_jr1965F (show 2 < v by linarith)).div_const
    (2*exp eulerMascheroniConstant)
  have he : wuLowerCoefficient (v-1)=log (v-2) := by
    simpa only [wuLowerCoefficient,show v-1-1=v-2 by ring] using
      jr1965f_normalized_firstInterval (s := v-1) (by linarith) (by linarith)
  have hn : v-1 ≠ 0 := by linarith
  have he' : jr1965f (v-1)/(2*exp eulerMascheroniConstant)=log (v-2)/(v-1) := by
    rw [← he]; unfold wuLowerCoefficient; field_simp [hn]
  exact h.congr_deriv he'

theorem low_derivative_error {v : ℝ} (hv : v ∈ Icc (3:ℝ) 4) :
    1/2-2/(v-1)^2-2*(v-3)^2/(v-1)^4-log (v-2)/(v-1) ≤ (v-3)^2/36 := by
  have hn : 0 < v-1 := by linarith [hv.1]
  have hl := div_le_div_of_nonneg_right (log_lower (show 1 ≤ v-2 by linarith [hv.1])) hn.le
  have hid : 1/2-2/(v-1)^2-2*(v-3)^2/(v-1)^4-lowerLog (v-2)/(v-1) =
      (v-3)^3*(3*(v-3)+8)/(6*(v-1)^4) := by
    unfold lowerLog
    have he : v-2+1=v-1 := by ring
    rw [he]; field_simp [hn.ne']; ring
  have hz : 0 ≤ v-3 ∧ v-3 ≤ 1 := by constructor <;> linarith [hv.1,hv.2]
  have hz0 := hz.1
  have hz1 : 0 ≤ 1-(v-3) := by linarith only [hz.2]
  have hp : 0 ≤ (v-3)^4+8*(v-3)^3+6*(v-3)^2+16*(1-(v-3)) := by positivity
  have hq : (v-3)^3*(3*(v-3)+8)/(6*(v-1)^4) ≤ (v-3)^2/36 := by
    apply (div_le_iff₀ (show 0 < 6*(v-1)^4 by positivity)).2
    have hm := mul_nonneg (sq_nonneg (v-3)) hp
    nlinarith only [hm]
  linarith only [hl,hid,hq]

/-- FTC/monotonicity integration of the original p derivative error. -/
theorem low_pointwise {v : ℝ} (hv : v ∈ Icc (3:ℝ) 4) :
    0 ≤ SharedRationalEnvelope.p v-wuUpperCoefficient v ∧
    SharedRationalEnvelope.p v-wuUpperCoefficient v ≤ (v-3)^3/108 := by
  let F : ℝ → ℝ := fun x => (x-3)^3/108-(SharedRationalEnvelope.p x-wuUpperCoefficient x)
  have hd (x : ℝ) (hx : x ∈ Icc (3:ℝ) 4) : HasDerivAt F
      ((x-3)^2/36-(1/2-2/(x-1)^2-2*(x-3)^2/(x-1)^4-log (x-2)/(x-1))) x := by
    convert (((((hasDerivAt_id x).sub_const 3).pow 3).div_const 108).sub
      ((p_derivative hx.1).sub (initial_derivative hx.1 (by linarith [hx.2])))) using 1 <;>
      first | rfl | (dsimp; ring)
  have hm : MonotoneOn F (Icc (3:ℝ) 4) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx; rw [(hd x (interior_subset hx)).deriv]
      exact sub_nonneg.mpr (low_derivative_error (interior_subset hx))
  have h := hm (by norm_num : (3:ℝ) ∈ Icc (3:ℝ) 4) hv hv.1
  have he : wuUpperCoefficient 3=1 := jr1965F_normalized_initial (by norm_num) le_rfl
  have hzero : F 3=0 := by norm_num [F,SharedRationalEnvelope.p,lowerLog,he]
  rw [hzero] at h
  dsimp only [F] at h
  exact ⟨sub_nonneg.mpr (SharedRationalEnvelope.upper_p hv.1 hv.2),by linarith only [h]⟩

/-- Full original signed weight is retained in the primary enclosures. -/
def weighted (p : ℝ → ℝ) (l r : ℝ) : ℝ := ∫ t in l..r, SharedRationalEnvelope.weight t*p (u t)

theorem weighted_integrable (p : ℝ → ℝ) (hp : Continuous p) {l r : ℝ}
    (hl : a ≤ l) (hr : r ≤ s) (ho : l ≤ r) :
    IntervalIntegrable (fun t => SharedRationalEnvelope.weight t*p (u t)) volume l r := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul
  · unfold SharedRationalEnvelope.weight
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    rw [uIcc_of_le ho] at ht
    have ht0 := truncatedSixthLower_parameters.1.trans_le (hl.trans ht.1)
    have hd : 0 < 1/2-t := by linarith [ht.2,hr,truncatedSixthLower_parameters.2.2.2.1]
    exact mul_ne_zero ht0.ne' hd.ne'
  · exact (hp.comp (by unfold u; fun_prop)).continuousOn

theorem middle_geometry {t : ℝ} (ht : t ∈ Icc (c 5) (c 4)) :
    0 < t ∧ 0 < 1/2-t ∧ u t ∈ Icc (4:ℝ) 5 := by
  have ha := truncatedSixthLower_parameters.1
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [a,c,truncatedSixthLowerAlpha] at ht; linarith
  · norm_num [a,c,truncatedSixthLowerAlpha] at ht; linarith
  · apply (le_div_iff₀ ha).2
    have h : t ≤ 1/2-4*a := ht.2; linarith
  · apply (div_le_iff₀ ha).2
    have h : 1/2-5*a ≤ t := ht.1; linarith

theorem middle_full_weight_enclosure :
    weighted middleLo (c 5) (c 4) ≤ middleKernel ∧
    middleKernel ≤ weighted middleHi (c 5) (c 4) := by
  have hl : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hr : c 4 ≤ s := SharedRationalEnvelope.window_order.2.1
  have ho : c 5 ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hk := kernel_integrable (fun v => GConvexChord.C+GConvexChord.m*v) hl hr ho (by fun_prop)
  have hiL := weighted_integrable middleLo (by unfold middleLo; fun_prop) hl hr ho
  have hiH := weighted_integrable middleHi (by unfold middleHi; fun_prop) hl hr ho
  constructor
  · apply intervalIntegral.integral_mono_on ho hiL hk
    intro t ht
    rw [HighSharedKernelMagnitude.kernel_density (fun v => GConvexChord.C+GConvexChord.m*v)]
    exact mul_le_mul_of_nonneg_left (middle_pointwise (middle_geometry ht).2.2).1
      (HighSharedKernelMagnitude.middle_weight ht).1
  · apply intervalIntegral.integral_mono_on ho hk hiH
    intro t ht
    rw [HighSharedKernelMagnitude.kernel_density (fun v => GConvexChord.C+GConvexChord.m*v)]
    exact mul_le_mul_of_nonneg_left (middle_pointwise (middle_geometry ht).2.2).2
      (HighSharedKernelMagnitude.middle_weight ht).1

theorem low_full_weight_enclosure : 0 ≤ lowKernel ∧
    lowKernel ≤ weighted (fun v => (v-3)^3/108) (c 4) s := by
  have ho := SharedRationalEnvelope.window_order
  have hp := SharedRationalEnvelope.p_continuous
  have hU : ContinuousOn (fun t => wuUpperCoefficient (u t)) (Icc (c 4) s) := by
    apply continuousOn_wuUpperCoefficient.comp (by unfold u; fun_prop)
    intro t ht
    change 0 < u t
    linarith [(SharedRationalEnvelope.geometry ht).2.2.1]
  have hw : ContinuousOn SharedRationalEnvelope.weight (Icc (c 4) s) := by
    unfold SharedRationalEnvelope.weight
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact mul_ne_zero (SharedRationalEnvelope.geometry ht).1.ne'
      (SharedRationalEnvelope.geometry ht).2.1.ne'
  have hi := (hw.mul (hp.sub hU)).intervalIntegrable_of_Icc (μ := volume) ho.2.1
  refine ⟨low_nonnegative,?_⟩
  rw [low_explicit]
  apply intervalIntegral.integral_mono_on ho.2.1 hi
    (weighted_integrable (fun v => (v-3)^3/108) (by fun_prop) ho.1 le_rfl ho.2.1)
  intro t ht
  exact mul_le_mul_of_nonneg_left
    (low_pointwise ⟨(SharedRationalEnvelope.geometry ht).2.2.1,(SharedRationalEnvelope.geometry ht).2.2.2⟩).2
    (HighSharedKernelMagnitude.low_weight ht).1

/-- Polynomial FTC keeps the entire net numerator, rather than freezing a total weight. -/
def netPrimitive (j A B C D k t : ℝ) : ℝ :=
  -k*a*((24*a*j-4)*A*(u t-j)+((24*a*j-4)*B+24*a*A)*(u t-j)^2/2+
    ((24*a*j-4)*C+24*a*B)*(u t-j)^3/3+
    ((24*a*j-4)*D+24*a*C)*(u t-j)^4/4+24*a*D*(u t-j)^5/5)

theorem net_derivative (j A B C D k t : ℝ) : HasDerivAt (netPrimitive j A B C D k)
    (k*(8-24*t)*(A+B*(u t-j)+C*(u t-j)^2+D*(u t-j)^3)) t := by
  have hd := (((hasDerivAt_const t (1/2:ℝ)).sub (hasDerivAt_id t)).div_const a).sub_const j
  convert! (((((hd.const_mul ((24*a*j-4)*A)).add
    ((hd.pow 2).const_mul ((24*a*j-4)*B+24*a*A) |>.div_const 2)).add
    ((hd.pow 3).const_mul ((24*a*j-4)*C+24*a*B) |>.div_const 3)).add
    ((hd.pow 4).const_mul ((24*a*j-4)*D+24*a*C) |>.div_const 4)).add
    ((hd.pow 5).const_mul (24*a*D) |>.div_const 5) |>.const_mul (-k*a)) using 1;
    first | rfl | (dsimp [u]; field_simp [truncatedSixthLower_parameters.1.ne']; ring)

theorem net_ftc (j A B C D k l r : ℝ) :
    (∫ t in l..r, k*(8-24*t)*(A+B*(u t-j)+C*(u t-j)^2+D*(u t-j)^3)) =
      netPrimitive j A B C D k r-netPrimitive j A B C D k l := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => net_derivative j A B C D k t)
  exact (by unfold u; fun_prop : Continuous (fun t => k*(8-24*t)*(A+B*(u t-j)+C*(u t-j)^2+D*(u t-j)^3))).intervalIntegrable _ _

/-- Reciprocal denominator bounds are proved on the original windows. -/
theorem middle_net_weight {t : ℝ} (ht : t ∈ Icc (c 5) (c 4)) :
    16*(8-24*t) ≤ SharedRationalEnvelope.weight t ∧
    SharedRationalEnvelope.weight t ≤ 22*(8-24*t) := by
  have hg := middle_geometry ht
  have hn : 0 ≤ 8-24*t := by norm_num [a,c,truncatedSixthLowerAlpha] at ht; linarith
  have hd := mul_pos hg.1 hg.2.1
  have hmax : t*(1/2-t) ≤ (1/16:ℝ) := by nlinarith [sq_nonneg (t-1/4)]
  have hmin : (1/22:ℝ) ≤ t*(1/2-t) := by
    have hp := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)
    norm_num [c,a,truncatedSixthLowerAlpha] at hp ht
    nlinarith only [hp,ht.1]
  unfold SharedRationalEnvelope.weight
  constructor
  · apply (le_div_iff₀ hd).2
    nlinarith only [mul_nonneg hn (sub_nonneg.mpr hmax)]
  · apply (div_le_iff₀ hd).2
    nlinarith only [mul_nonneg hn (sub_nonneg.mpr hmin)]

theorem low_net_weight {t : ℝ} (ht : t ∈ Icc (c 4) s) :
    SharedRationalEnvelope.weight t ≤ 17*(8-24*t) := by
  have hg := SharedRationalEnvelope.geometry ht
  have hn : 0 ≤ 8-24*t := by norm_num [s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma] at ht; linarith
  have hd := mul_pos hg.1 hg.2.1
  have hmin : (1/17:ℝ) ≤ t*(1/2-t) := by
    have hp := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)
    norm_num [c,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma] at hp ht
    nlinarith only [hp,ht.1,ht.2]
  unfold SharedRationalEnvelope.weight
  apply (div_le_iff₀ hd).2
  nlinarith only [mul_nonneg hn (sub_nonneg.mpr hmin)]

theorem middle_poly_nonnegative {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    0 ≤ middleLo v ∧ 0 ≤ middleHi v := by
  have h1 : 0 ≤ 5-v := by linarith [hv.2]
  have h2 : 0 ≤ v-4 := by linarith [hv.1]
  norm_num [middleLo,middleHi,GConvexChord.r4,GConvexChord.r5]
  constructor <;> positivity

def middleLowerPayment : ℝ :=
  netPrimitive 4 (GConvexChord.r4-287/250)
    ((GConvexChord.r5-9044059/6431250)-(GConvexChord.r4-287/250)+1/144) (-1/144) 0 16 (c 4)-
  netPrimitive 4 (GConvexChord.r4-287/250)
    ((GConvexChord.r5-9044059/6431250)-(GConvexChord.r4-287/250)+1/144) (-1/144) 0 16 (c 5)
def middleUpperPayment : ℝ :=
  netPrimitive 4 (GConvexChord.r4-34832/30375)
    ((GConvexChord.r5-541588/385875)-(GConvexChord.r4-34832/30375)+1/22) (-1/22) 0 22 (c 4)-
  netPrimitive 4 (GConvexChord.r4-34832/30375)
    ((GConvexChord.r5-541588/385875)-(GConvexChord.r4-34832/30375)+1/22) (-1/22) 0 22 (c 5)
def lowUpperPayment : ℝ := netPrimitive 3 0 0 0 (1/108) 17 s-netPrimitive 3 0 0 0 (1/108) 17 (c 4)

theorem middle_payments : middleLowerPayment ≤ middleKernel ∧ middleKernel ≤ middleUpperPayment := by
  have ho : c 5 ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hl : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hr := SharedRationalEnvelope.window_order.2.1
  have hL := weighted_integrable middleLo (by unfold middleLo; fun_prop) hl hr ho
  have hH := weighted_integrable middleHi (by unfold middleHi; fun_prop) hl hr ho
  have hcL : Continuous (fun t => 16*(8-24*t)*middleLo (u t)) := by unfold middleLo u; fun_prop
  have hcH : Continuous (fun t => 22*(8-24*t)*middleHi (u t)) := by unfold middleHi u; fun_prop
  have hmL := intervalIntegral.integral_mono_on ho (hcL.intervalIntegrable _ _) hL
    (fun t ht => mul_le_mul_of_nonneg_right (middle_net_weight ht).1 (middle_poly_nonnegative (middle_geometry ht).2.2).1)
  have hmH := intervalIntegral.integral_mono_on ho hH (hcH.intervalIntegrable _ _)
    (fun t ht => mul_le_mul_of_nonneg_right (middle_net_weight ht).2 (middle_poly_nonnegative (middle_geometry ht).2.2).2)
  have eL : (∫ t in c 5..c 4, 16*(8-24*t)*middleLo (u t))=middleLowerPayment := by
    unfold middleLo middleLowerPayment
    rw [← net_ftc]
    apply intervalIntegral.integral_congr
    intro t ht; ring
  have eH : (∫ t in c 5..c 4, 22*(8-24*t)*middleHi (u t))=middleUpperPayment := by
    unfold middleHi middleUpperPayment
    rw [← net_ftc]
    apply intervalIntegral.integral_congr
    intro t ht; ring
  rw [eL] at hmL
  rw [eH] at hmH
  exact ⟨hmL.trans middle_full_weight_enclosure.1,middle_full_weight_enclosure.2.trans hmH⟩

theorem low_payment : lowKernel ≤ lowUpperPayment := by
  have ho := SharedRationalEnvelope.window_order
  have hi := weighted_integrable (fun v => (v-3)^3/108) (by fun_prop) ho.1 le_rfl ho.2.1
  have hc : Continuous (fun t => 17*(8-24*t)*((u t-3)^3/108)) := by unfold u; fun_prop
  have hm := intervalIntegral.integral_mono_on ho.2.1 hi (hc.intervalIntegrable _ _)
    (fun t ht => mul_le_mul_of_nonneg_right (low_net_weight ht) (by
      have h : 0 ≤ u t-3 := by linarith [(SharedRationalEnvelope.geometry ht).2.2.1]
      positivity))
  have he : (∫ t in c 4..s, 17*(8-24*t)*((u t-3)^3/108))=lowUpperPayment := by
    unfold lowUpperPayment
    rw [← net_ftc]
    apply intervalIntegral.integral_congr
    intro t ht; ring
  rw [he] at hm
  exact low_full_weight_enclosure.2.trans hm

theorem middle_magnitude : (1/50:ℝ) < middleKernel ∧ middleKernel < 23/250 := by
  have h : (1/50:ℝ) < middleLowerPayment ∧ middleUpperPayment < 23/250 := by
    norm_num [middleLowerPayment,middleUpperPayment,netPrimitive,u,c,a,truncatedSixthLowerAlpha,GConvexChord.r4,GConvexChord.r5]
  exact ⟨h.1.trans_le middle_payments.1,middle_payments.2.trans_lt h.2⟩

theorem low_magnitude : 0 ≤ lowKernel ∧ lowKernel < (1/100:ℝ) := by
  have h : lowUpperPayment < (1/100:ℝ) := by
    norm_num [lowUpperPayment,netPrimitive,u,c,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  exact ⟨low_nonnegative,low_payment.trans_lt h⟩

def gEnvelope (f : ℝ → ℝ) : ℝ :=
  (8/a)*(42823/151875)*(upperLog (c 5/a)-f (c 5/a))+
  8*(GConvexChord.m/a+2*GConvexChord.C)*(upperLog (c 4/c 5)-f (c 4/c 5))+
  8*VariableGIntegral.logCoefficient*(upperLog (s/c 4)-f (s/c 4))+
  8*(upperLog (6*a/s)-f (6*a/s))
def gLowerPayment : ℝ := gEnvelope JointLogTotalComparison.V
def gUpperPayment : ℝ := gEnvelope lowerLog

theorem g_payments : gLowerPayment ≤ AnalyticTotalThreshold.gLoss ∧
    AnalyticTotalThreshold.gLoss ≤ gUpperPayment := by
  have h1 := log_lower (show 1 ≤ c 5/a by norm_num [c,a,truncatedSixthLowerAlpha])
  have h2 := log_lower (show 1 ≤ c 4/c 5 by norm_num [c,a,truncatedSixthLowerAlpha])
  have h3 := log_lower (show 1 ≤ s/c 4 by norm_num [s,c,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h4 := log_lower (show 1 ≤ 6*a/s by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h5 := JointLogTotalComparison.log_le_V (show 1 ≤ c 5/a by norm_num [c,a,truncatedSixthLowerAlpha])
  have h6 := JointLogTotalComparison.log_le_V (show 1 ≤ c 4/c 5 by norm_num [c,a,truncatedSixthLowerAlpha])
  have h7 := JointLogTotalComparison.log_le_V (show 1 ≤ s/c 4 by norm_num [s,c,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h8 := JointLogTotalComparison.log_le_V (show 1 ≤ 6*a/s by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  rw [g_exact]
  unfold gLogRemainder gLowerPayment gUpperPayment gEnvelope
  norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma,GConvexChord.C,GConvexChord.m,
    GConvexChord.r4,GConvexChord.r5,VariableGIntegral.logCoefficient,VariableGIntegral.a,
    JointLogTotalComparison.V,upperLog,lowerLog] at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  constructor <;> linarith only [h1,h2,h3,h4,h5,h6,h7,h8]

def baseUpperPayment : ℝ :=
  32*(JointLogTotalComparison.V (3/2)-lowerLog (3/2))+
  16*(JointLogTotalComparison.V (26/25)-lowerLog (26/25))+8/12500

theorem base_payment : AnalyticTotalThreshold.baseLoss ≤ baseUpperPayment := by
  have h1 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ)≤3/2)
  have h2 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ)≤26/25)
  have hb := HighSharedKernelMagnitude.beta_bound
  rw [base_exact]
  unfold baseLogRemainder baseUpperPayment
  linarith only [h1,h2,hb]

/-- Export the already-proved high comparison without its coarse decimal rounding. -/
def highUpperPayment : ℝ := HighSharedKernelMagnitude.highCapPrimitive (c 5)-
  HighSharedKernelMagnitude.highCapPrimitive a

theorem high_payment : highKernel ≤ highUpperPayment := by
  have ho : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hs : c 5 ≤ s := by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hi := kernel_integrable (fun v => (42823/151875)*v) le_rfl hs ho (by fun_prop)
  have hc : Continuous HighSharedKernelMagnitude.highCapDensity := by
    unfold HighSharedKernelMagnitude.highCapDensity; fun_prop
  have hm := intervalIntegral.integral_mono_on ho hi (hc.intervalIntegrable _ _) (fun t ht => ?_)
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => HighSharedKernelMagnitude.highCap_derivative t) (hc.intervalIntegrable _ _)] at hm
    exact hm
  have hg := HighSharedKernelMagnitude.high_geometry ht
  have hb := HighSharedKernelMagnitude.high_pointwise hg.2.2.1 hg.2.2.2
  have hw := HighSharedKernelMagnitude.high_weight ht
  rw [HighSharedKernelMagnitude.kernel_density (fun v => (42823/151875)*v)]
  have hn : 0 ≤ (42823/151875)*u t-wuUpperCoefficient (u t) := by linarith only [hb.1]
  have he : u t-5=(c 5-t)/a := by unfold u c; field_simp [truncatedSixthLower_parameters.1.ne']; ring
  have h := mul_le_mul hw.2 hb.2 hn (by norm_num : (0:ℝ)≤200)
  rw [he] at h
  convert h using 1 <;> first | rfl | (unfold HighSharedKernelMagnitude.highCapDensity; ring)

/-- Exact rational bilateral total; no constituent payment is reused. -/
def triple : ℝ := AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+AnalyticTotalThreshold.sharedLoss
def tripleLowerPayment : ℝ := gLowerPayment+HighSharedKernelMagnitude.highRecovery+middleLowerPayment
def tripleUpperPayment : ℝ := baseUpperPayment+gUpperPayment+highUpperPayment+middleUpperPayment+lowUpperPayment

theorem triple_payments : tripleLowerPayment ≤ triple ∧ triple ≤ tripleUpperPayment := by
  have hn := AnalyticTotalThreshold.signed_losses_nonnegative.1
  unfold triple
  rw [shared_exact]
  unfold tripleLowerPayment tripleUpperPayment
  constructor
  · linarith only [hn,g_payments.1,HighSharedKernelMagnitude.high_recovery,middle_payments.1,low_nonnegative]
  · linarith only [base_payment,g_payments.2,high_payment,middle_payments.2,low_payment]

theorem rational_payment_bounds :
    (652/10000:ℝ) < tripleLowerPayment ∧ tripleUpperPayment < 2258/10000 ∧
    (7/500:ℝ) < gLowerPayment ∧ gUpperPayment < 19/500 ∧ baseUpperPayment < 1/200 ∧
    highUpperPayment < 17/200 ∧ lowUpperPayment < 9/1000 := by
  norm_num [tripleLowerPayment,tripleUpperPayment,gLowerPayment,gUpperPayment,gEnvelope,
    baseUpperPayment,highUpperPayment,middleLowerPayment,middleUpperPayment,lowUpperPayment,
    HighSharedKernelMagnitude.highCapPrimitive,HighSharedKernelMagnitude.highRecovery,
    netPrimitive,u,a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma,GConvexChord.C,
    GConvexChord.m,GConvexChord.r4,GConvexChord.r5,VariableGIntegral.logCoefficient,VariableGIntegral.a,
    JointLogTotalComparison.V,upperLog,lowerLog]

theorem triple_magnitude : (652/10000:ℝ) < triple ∧ triple < 2258/10000 :=
  ⟨rational_payment_bounds.1.trans_le triple_payments.1,
    triple_payments.2.trans_lt rational_payment_bounds.2.1⟩

/-- Both full recoveries, each spent once. This is still a certificate below actual Q. -/
def coefficient : ℝ := JointSixthFourDiagnostic.coefficient+
  (triple+FifthActualIntegralRecovery.recovery)/4

theorem coefficient_relation : coefficient = FifthLogTotalMagnitude.coefficient+
    (triple-BaseGSharedActualRecovery.recovery)/4 := by
  unfold coefficient FifthLogTotalMagnitude.coefficient
  rw [BaseGSharedActualRecovery.recovery_exact]
  ring

theorem remaining_error_exact : JointHMotherPayment.unroundedCoefficient-coefficient =
    ((AnalyticTotalThreshold.jLoss-JointJLossStrength.recovery)+
      (fifthPairFlin-FifthActualIntegralRecovery.logIntegral)+
      (truncatedSixthLowerF6lin-ClassicalLossBottleneck.sixthLogIntegral)+
      (AnalyticTotalThreshold.fourLoss-FourActualCapRecovery.recovery))/4 := by
  have h := FifthLogTotalMagnitude.seven_error_identity
  rw [coefficient_relation]
  unfold triple
  rw [BaseGSharedActualRecovery.recovery_exact]
  linarith only [h]

theorem coefficient_le_actual : coefficient ≤ JointHMotherPayment.unroundedCoefficient := by
  have hj := JointJLossStrength.actual_jLoss_lower
  have h5 := FifthActualIntegralRecovery.fifth_loss_localization.1
  have h6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.1
  have h4 := FourActualCapRecovery.actual_fourLoss_lower
  have he := remaining_error_exact
  unfold FifthActualIntegralRecovery.recovery AnalyticTotalThreshold.fifthLoss at h5
  linarith only [hj,h5,h6,h4,he]

/-- Exact target ledger, not an inference from an insufficient lower certificate. -/
theorem target_exact_difference : AnalyticTotalThreshold.target-coefficient =
    JointLogTotalComparison.rationalDeficit-Phase18.g18-Phase20.psiPaymentLoss-
    JointLogTotalComparison.logRemainder-
    (JointJLossStrength.recovery-JointJLossStrength.fixedRecovery)/4-
    JointLogTotalComparison.targetSlack-
    TotalEndpointComparison.quad/4*(TotalEndpointComparison.D-FifthClassicalShape.ell)^2-
    (ClassicalLossBottleneck.sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint)/4-
    FourActualCapRecovery.recovery/4-FifthActualIntegralRecovery.recovery/4-triple/4 := by
  have h := FifthLogTotalMagnitude.target_exact_difference
  rw [coefficient_relation,BaseGSharedActualRecovery.recovery_exact]
  linarith only [h]

theorem total_target_localization : -(2/25:ℝ) < AnalyticTotalThreshold.target-coefficient ∧
    AnalyticTotalThreshold.target-coefficient < 63/500 := by
  have h := FifthLogTotalMagnitude.total_target_localization
  have ht := triple_magnitude
  rw [coefficient_relation,BaseGSharedActualRecovery.recovery_exact]
  constructor <;> linarith only [h.1,h.2,ht.1,ht.2]

theorem combined_payment_magnitude : (113/5000:ℝ) < coefficient-JointSixthFourDiagnostic.coefficient ∧
    coefficient-JointSixthFourDiagnostic.coefficient < 79/1000 := by
  have ht := triple_magnitude
  have h5 := FifthLogTotalMagnitude.recovery_decimal_rational_bounds
  unfold coefficient
  constructor <;> linarith only [ht.1,ht.2,h5.1,h5.2]

end
end Wu2008DoubleSieve.JointSharedTightEnclosure
