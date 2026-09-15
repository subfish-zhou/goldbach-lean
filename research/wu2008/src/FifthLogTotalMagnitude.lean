import FifthActualIntegralRecovery
import BaseGSharedActualRecovery

namespace Wu2008DoubleSieve.FifthLogTotalMagnitude
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpMassBalance SharpLogRecurrence
open scoped Interval
noncomputable section

/-- Fixed envelopes at the two original geometric parameter endpoints. -/
def lo (z : ℝ) : ℝ := lowerLog (4/3)+lowerLog (3/2)+lowerLog ((z-1)/2)
def hi (z : ℝ) : ℝ := JointLogTotalComparison.V (4/3)+JointLogTotalComparison.V (3/2)+
  JointLogTotalComparison.V ((z-1)/2)
def f0 : ℝ := lo s0/s0
def slope : ℝ := (lo FifthClassicalShape.q/FifthClassicalShape.q-f0)/(FifthClassicalShape.q-s0)
def cap : ℝ := 1/(FifthClassicalShape.q-1)+
  (hi FifthClassicalShape.q-FifthClassicalShape.q/(FifthClassicalShape.q-1))/s0

theorem endpoint_logs {z : ℝ} (hz : 3 ≤ z) : lo z ≤ log (z-1) ∧ log (z-1) ≤ hi z := by
  have he : log (z-1) = log (4/3:ℝ)+log (3/2:ℝ)+log ((z-1)/2) := by
    rw [← log_mul (by norm_num : (4/3:ℝ) ≠ 0) (by norm_num : (3/2:ℝ) ≠ 0)]
    rw [← log_mul (by norm_num : (4/3:ℝ)*(3/2) ≠ 0) (show (z-1)/2 ≠ 0 by linarith)]
    congr 1
    ring
  have h1 := log_lower (by norm_num : (1:ℝ) ≤ 4/3)
  have h2 := log_lower (by norm_num : (1:ℝ) ≤ 3/2)
  have h3 := log_lower (show 1 ≤ (z-1)/2 by linarith)
  have h4 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 4/3)
  have h5 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 3/2)
  have h6 := JointLogTotalComparison.log_le_V (show 1 ≤ (z-1)/2 by linarith)
  unfold lo hi
  rw [he]
  constructor <;> linarith only [h1,h2,h3,h4,h5,h6]

/-- The global tangent inequality, not a truncation of a Taylor expansion. -/
theorem log_tangent {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    log t ≤ log m+(t-m)/m := by
  have h := log_le_sub_one_of_pos (div_pos ht hm)
  rw [log_div ht.ne' hm.ne'] at h
  have he : t/m-1=(t-m)/m := by field_simp
  rw [he] at h
  linarith only [h]

/-- Concavity on the original interval, obtained by cancelling two tangent errors. -/
theorem log_chord {l t r : ℝ} (hl : 0 < l) (hlt : l ≤ t) (htr : t ≤ r) (hlr : l < r) :
    ((r-t)*log l+(t-l)*log r)/(r-l) ≤ log t := by
  have ht := hl.trans_le hlt
  have hr := ht.trans_le htr
  have h1 := mul_le_mul_of_nonneg_left (log_tangent hl ht) (sub_nonneg.mpr htr)
  have h2 := mul_le_mul_of_nonneg_left (log_tangent hr ht) (sub_nonneg.mpr hlt)
  apply (div_le_iff₀ (sub_pos.mpr hlr)).2
  have he : (r-t)*(log t+(l-t)/t)+(t-l)*(log t+(r-t)/t) = log t*(r-l) := by
    field_simp
    ring
  linarith only [h1,h2,he]

theorem scalar_bounds {z : ℝ} (hz : s0 ≤ z) (hq : z ≤ FifthClassicalShape.q) :
    f0+slope*(z-s0) ≤ log (z-1)/z ∧ log (z-1)/z ≤ cap := by
  have hp := FifthClassicalShape.parameters
  have hs : 0 < s0 := by linarith [hp.1]
  have hz0 := hs.trans_le hz
  have hq0 := hs.trans hp.2.1
  have hd := sub_pos.mpr hp.2.1
  have hL := (endpoint_logs hp.1.le).1
  have hQ := endpoint_logs (show 3 ≤ FifthClassicalShape.q by linarith [hp.1,hp.2.1])
  have hc := log_chord (show 0 < s0-1 by linarith [hp.1])
    (show s0-1 ≤ z-1 by linarith) (show z-1 ≤ FifthClassicalShape.q-1 by linarith)
    (show s0-1 < FifthClassicalShape.q-1 by linarith [hp.2.1])
  have hh1 := mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr hq)
  have hh2 := mul_le_mul_of_nonneg_left hQ.1 (sub_nonneg.mpr hz)
  have hch : ((FifthClassicalShape.q-z)*lo s0+(z-s0)*lo FifthClassicalShape.q)/
      (FifthClassicalShape.q-s0) ≤ log (z-1) := by
    apply (div_le_iff₀ hd).2
    have hc' := (div_le_iff₀ (show 0 < (FifthClassicalShape.q-1)-(s0-1) by linarith)).1 hc
    nlinarith only [hh1,hh2,hc']
  have hsl : 0 ≤ slope := by
    norm_num [slope,f0,lo,FifthClassicalShape.q,s0,lowerLog,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hid : (((FifthClassicalShape.q-z)*lo s0+(z-s0)*lo FifthClassicalShape.q)/
      (FifthClassicalShape.q-s0))/z = f0+slope*(z-s0)*(FifthClassicalShape.q/z) := by
    unfold slope f0
    field_simp
    ring
  have hlower := div_le_div_of_nonneg_right hch hz0.le
  rw [hid] at hlower
  have hmul := mul_le_mul_of_nonneg_left (show 1 ≤ FifthClassicalShape.q/z from (le_div_iff₀ hz0).2 (by simpa using hq))
    (mul_nonneg hsl (sub_nonneg.mpr hz))
  constructor
  · nlinarith only [hlower,hmul]
  · have ht := log_tangent (show 0 < z-1 by linarith [hp.1,hz])
      (show 0 < FifthClassicalShape.q-1 by linarith [hp.1,hp.2.1])
    have hc0 : 0 ≤ hi FifthClassicalShape.q-FifthClassicalShape.q/(FifthClassicalShape.q-1) := by
      norm_num [hi,JointLogTotalComparison.V,lowerLog,upperLog,FifthClassicalShape.q,a,truncatedSixthLowerAlpha]
    rw [show z-1-(FifthClassicalShape.q-1)=z-FifthClassicalShape.q by ring] at ht
    have hdiv := div_le_div_of_nonneg_right (show log (z-1) ≤ hi FifthClassicalShape.q+
        (z-FifthClassicalShape.q)/(FifthClassicalShape.q-1) by linarith only [ht,hQ.2]) hz0.le
    have hrec := div_le_div_of_nonneg_left hc0 hs hz
    have he : (hi FifthClassicalShape.q+(z-FifthClassicalShape.q)/(FifthClassicalShape.q-1))/z =
      1/(FifthClassicalShape.q-1)+(hi FifthClassicalShape.q-
      FifthClassicalShape.q/(FifthClassicalShape.q-1))/z := by field_simp; ring
    rw [he] at hdiv
    unfold cap
    linarith only [hdiv,hrec]

/-- Affine in the shared sum; the reciprocal product is never corner-frozen. -/
def kernel (p k x y : ℝ) : ℝ := (p+k*(2*b-x-y))/(x*y)
def inner (p k y : ℝ) : ℝ := ((p+k*(2*b-y))*(log y-log a)-k*(y-a))/y
def primitive (p k y : ℝ) : ℝ := (p/2+k*b)*(log y-log a)^2-k*(y-a)*(log y-log a)
def endpoint (p k : ℝ) : ℝ := 2*p*(log b-log a)^2+
  4*k*(b*(log b-log a)^2-(b-a)*(log b-log a))

theorem inner_ftc (p k : ℝ) {y : ℝ} (hy : a ≤ y) :
    (∫ x in a..y, kernel p k x y) = inner p k y := by
  have ha := truncatedSixthLower_parameters.1
  have hy0 := ha.trans_le hy
  have hn (x : ℝ) (hx : x ∈ uIcc a y) : x ≠ 0 := by
    rw [uIcc_of_le hy] at hx
    exact (ha.trans_le hx.1).ne'
  have hi : IntervalIntegrable (fun x => kernel p k x y) volume a y := by
    apply ContinuousOn.intervalIntegrable
    unfold kernel
    exact (continuousOn_const.add (continuousOn_const.mul
      ((continuousOn_const.sub continuousOn_id).sub continuousOn_const))).div
      (continuousOn_id.mul continuousOn_const) (fun x hx => mul_ne_zero (hn x hx) hy0.ne')
  have hd (x : ℝ) (hx : x ∈ uIcc a y) : HasDerivAt
      (fun x => ((p+k*(2*b-y))*log x-k*x)/y) (kernel p k x y) x := by
    convert (((hasDerivAt_log (hn x hx)).const_mul (p+k*(2*b-y))).sub
      ((hasDerivAt_id x).const_mul k) |>.div_const y) using 1 <;>
      first | rfl | (dsimp [kernel]; field_simp [hn x hx,hy0.ne']; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  dsimp [inner]
  ring

theorem primitive_derivative (p k : ℝ) {y : ℝ} (hy : a ≤ y) :
    HasDerivAt (primitive p k) (inner p k y) y := by
  have hlog := (hasDerivAt_log (truncatedSixthLower_parameters.1.trans_le hy).ne').sub_const (log a)
  convert ((hlog.pow 2).const_mul (p/2+k*b)).sub
    ((((hasDerivAt_id y).sub_const a).const_mul k).mul hlog) using 1 <;>
    first | rfl | (dsimp [inner]; field_simp [(truncatedSixthLower_parameters.1.trans_le hy).ne']; ring)

theorem endpoint_comparison (p k : ℝ)
    (h : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
      kernel p k x y ≤ FifthActualIntegralRecovery.logRegular x y) :
    endpoint p k ≤ FifthActualIntegralRecovery.logIntegral := by
  have hp := truncatedSixthLower_parameters
  have hm : Continuous (fun y : ℝ => ∫ x in a..y, FifthActualIntegralRecovery.logRegular x y) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => FifthActualIntegralRecovery.logRegular x y)
    · exact FifthActualIntegralRecovery.log_continuous.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hn (y : ℝ) (hy : y ∈ uIcc a b) : y ≠ 0 := by
    rw [uIcc_of_le hp.2.1.le] at hy
    exact (hp.1.trans_le hy.1).ne'
  have hil : ContinuousOn (fun y : ℝ => log y-log a) (uIcc a b) :=
    (continuousOn_id.log (fun y hy => hn y hy)).sub continuousOn_const
  have hi : IntervalIntegrable (inner p k) volume a b := by
    apply ContinuousOn.intervalIntegrable
    unfold inner
    exact (((continuousOn_const.add (continuousOn_const.mul
      (continuousOn_const.sub continuousOn_id))).mul hil).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).div
      continuousOn_id (fun y hy => hn y hy)
  have hpoint (y : ℝ) (hy : y ∈ Icc a b) : inner p k y ≤
      ∫ x in a..y, FifthActualIntegralRecovery.logRegular x y := by
    rw [← inner_ftc p k hy.1]
    have hik : IntervalIntegrable (fun x => kernel p k x y) volume a y := by
      apply ContinuousOn.intervalIntegrable
      unfold kernel
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        rw [uIcc_of_le hy.1] at hx
        exact mul_ne_zero (hp.1.trans_le hx.1).ne' (hp.1.trans_le hy.1).ne'
    exact intervalIntegral.integral_mono_on hy.1 hik
      ((FifthActualIntegralRecovery.log_continuous.comp (f := fun x : ℝ => (x,y))
        (by fun_prop)).intervalIntegrable a y) (fun x hx => h x y hx.1 hx.2 hy.2)
  have hh := intervalIntegral.integral_mono_on hp.2.1.le hi (hm.intervalIntegrable a b) hpoint
  have hd (y : ℝ) (hy : y ∈ uIcc a b) := primitive_derivative p k
    (show a ≤ y by rw [uIcc_of_le hp.2.1.le] at hy; exact hy.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi] at hh
  unfold endpoint FifthActualIntegralRecovery.logIntegral
  dsimp [primitive] at hh
  linarith only [hh]

theorem endpoint_upper_comparison (p k : ℝ)
    (h : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
      FifthActualIntegralRecovery.logRegular x y ≤ kernel p k x y) :
    FifthActualIntegralRecovery.logIntegral ≤ endpoint p k := by
  have hp := truncatedSixthLower_parameters
  have hm : Continuous (fun y : ℝ => ∫ x in a..y, FifthActualIntegralRecovery.logRegular x y) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => FifthActualIntegralRecovery.logRegular x y)
    · exact FifthActualIntegralRecovery.log_continuous.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hn (y : ℝ) (hy : y ∈ uIcc a b) : y ≠ 0 := by
    rw [uIcc_of_le hp.2.1.le] at hy
    exact (hp.1.trans_le hy.1).ne'
  have hil : ContinuousOn (fun y : ℝ => log y-log a) (uIcc a b) :=
    (continuousOn_id.log (fun y hy => hn y hy)).sub continuousOn_const
  have hi : IntervalIntegrable (inner p k) volume a b := by
    apply ContinuousOn.intervalIntegrable
    unfold inner
    exact (((continuousOn_const.add (continuousOn_const.mul
      (continuousOn_const.sub continuousOn_id))).mul hil).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).div
      continuousOn_id (fun y hy => hn y hy)
  have hpoint (y : ℝ) (hy : y ∈ Icc a b) : (∫ x in a..y, FifthActualIntegralRecovery.logRegular x y) ≤ inner p k y := by
    rw [← inner_ftc p k hy.1]
    have hik : IntervalIntegrable (fun x => kernel p k x y) volume a y := by
      apply ContinuousOn.intervalIntegrable
      unfold kernel
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        rw [uIcc_of_le hy.1] at hx
        exact mul_ne_zero (hp.1.trans_le hx.1).ne' (hp.1.trans_le hy.1).ne'
    exact intervalIntegral.integral_mono_on hy.1
      ((FifthActualIntegralRecovery.log_continuous.comp (f := fun x : ℝ => (x,y))
        (by fun_prop)).intervalIntegrable a y) hik (fun x hx => h x y hx.1 hx.2 hy.2)
  have hh := intervalIntegral.integral_mono_on hp.2.1.le (hm.intervalIntegrable a b) hi hpoint
  have hd (y : ℝ) (hy : y ∈ uIcc a b) := primitive_derivative p k
    (show a ≤ y by rw [uIcc_of_le hp.2.1.le] at hy; exact hy.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi] at hh
  unfold endpoint FifthActualIntegralRecovery.logIntegral
  dsimp [primitive] at hh
  linarith only [hh]

/-- Both inequalities concern the complete original log integrand. -/
theorem kernel_bounds {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    kernel (f0/a) (slope/a^2) x y ≤ FifthActualIntegralRecovery.logRegular x y ∧
    FifthActualIntegralRecovery.logRegular x y ≤ kernel (cap/a) 0 x y := by
  have ha := truncatedSixthLower_parameters.1
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hp := FifthActualIntegralRecovery.parameter_range hx hxy hy
  have hh := scalar_bounds hp.1 hp.2
  have h1 := div_le_div_of_nonneg_right hh.1 (mul_pos ha (mul_pos hx0 hy0)).le
  have h2 := div_le_div_of_nonneg_right hh.2 (mul_pos ha (mul_pos hx0 hy0)).le
  have hz : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
    linarith [hxy.trans hy]
  rw [FifthActualIntegralRecovery.log_literal hx hxy hy]
  constructor
  · convert h1 using 1 <;> first | rfl |
      (dsimp [kernel,s0,truncatedSixthLowerS,truncatedSixthLowerC];
       field_simp [ha.ne',hx0.ne',hy0.ne',hz.ne']; ring)
  · convert h2 using 1 <;> first | rfl |
      (dsimp [kernel,truncatedSixthLowerS,truncatedSixthLowerC];
       field_simp [ha.ne',hx0.ne',hy0.ne',hz.ne']; ring)

theorem integral_bounds : endpoint (f0/a) (slope/a^2) ≤ FifthActualIntegralRecovery.logIntegral ∧
    FifthActualIntegralRecovery.logIntegral ≤ endpoint (cap/a) 0 :=
  ⟨endpoint_comparison _ _ (fun _ _ hx hxy hy => (kernel_bounds hx hxy hy).1),
   endpoint_upper_comparison _ _ (fun _ _ hx hxy hy => (kernel_bounds hx hxy hy).2)⟩

def lowerQuad : ℝ := 2*(f0/a-fifthDensity)+4*(slope/a^2-FifthClassicalShape.k)*b
def lowerLin : ℝ := 4*(slope/a^2-FifthClassicalShape.k)*(b-a)
def upperQuad : ℝ := 2*(cap/a-fifthDensity)-4*FifthClassicalShape.k*b
def upperLin : ℝ := 4*FifthClassicalShape.k*(b-a)
def dLower : ℝ := lowerLog (b/a)
def dUpper : ℝ := JointLogTotalComparison.V (b/a)
def lowerPayment : ℝ := lowerQuad*dLower^2-lowerLin*dUpper
def upperPayment : ℝ := upperQuad*dLower^2+upperLin*dUpper

theorem rational_signs : 0 ≤ lowerQuad ∧ 0 ≤ lowerLin ∧ upperQuad ≤ 0 ∧ 0 ≤ upperLin ∧
    0 ≤ dLower ∧ (1/40:ℝ) < lowerPayment ∧ upperPayment < 901/10000 := by
  norm_num [lowerPayment,upperPayment,lowerQuad,lowerLin,upperQuad,upperLin,dLower,dUpper,
    cap,hi,lo,f0,slope,JointLogTotalComparison.V,lowerLog,upperLog,fifthDensity,
    FifthClassicalShape.k,FifthClassicalShape.c,FifthClassicalShape.f,FifthClassicalShape.q,
    s0,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem log_ratio_bounds : dLower ≤ log b-log a ∧ log b-log a ≤ dUpper := by
  have h : (1:ℝ) ≤ b/a := by norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta]) (by norm_num [a,truncatedSixthLowerAlpha])]
  exact ⟨log_lower h,JointLogTotalComparison.log_le_V h⟩

/-- Analytic full-domain magnitude, with no numerical logarithm evaluation. -/
theorem recovery_enclosure : lowerPayment ≤ FifthActualIntegralRecovery.recovery ∧
    FifthActualIntegralRecovery.recovery ≤ upperPayment := by
  have hi := integral_bounds
  have hl := log_ratio_bounds
  have hs := rational_signs
  have hsq := pow_le_pow_left₀ hs.2.2.2.2.1 hl.1 2
  have hp := mul_le_mul_of_nonneg_left hsq hs.1
  have hm := mul_le_mul_of_nonneg_left hl.2 hs.2.1
  have hu := mul_le_mul_of_nonpos_left hsq hs.2.2.1
  have hv := mul_le_mul_of_nonneg_left hl.2 hs.2.2.2.1
  have he1 : endpoint (f0/a) (slope/a^2)-AnalyticTotalThreshold.fifthEndpoint =
      lowerQuad*(log b-log a)^2-lowerLin*(log b-log a) := by
    unfold endpoint AnalyticTotalThreshold.fifthEndpoint lowerQuad lowerLin
    change 2*(f0/a)*(log b-log a)^2+4*(slope/a^2)*(b*(log b-log a)^2-(b-a)*(log b-log a))-
      (2*fifthDensity*(log b-log a)^2+4*FifthClassicalShape.k*(b*(log b-log a)^2-(b-a)*(log b-log a))) = _
    ring
  have he2 : endpoint (cap/a) 0-AnalyticTotalThreshold.fifthEndpoint =
      upperQuad*(log b-log a)^2+upperLin*(log b-log a) := by
    unfold endpoint AnalyticTotalThreshold.fifthEndpoint upperQuad upperLin
    change 2*(cap/a)*(log b-log a)^2+4*0*(b*(log b-log a)^2-(b-a)*(log b-log a))-
      (2*fifthDensity*(log b-log a)^2+4*FifthClassicalShape.k*(b*(log b-log a)^2-(b-a)*(log b-log a))) = _
    ring
  unfold lowerPayment upperPayment FifthActualIntegralRecovery.recovery
  constructor <;> linarith only [hi.1,hi.2,he1,he2,hp,hm,hu,hv]

theorem recovery_magnitude : (1/40:ℝ) < FifthActualIntegralRecovery.recovery ∧
    FifthActualIntegralRecovery.recovery < 901/10000 := by
  have hs := rational_signs
  exact ⟨hs.2.2.2.2.2.1.trans_le recovery_enclosure.1,
    recovery_enclosure.2.trans_lt hs.2.2.2.2.2.2⟩

/-- Rational endpoint arithmetic gives a narrower readable export of the same enclosure. -/
theorem recovery_decimal_rational_bounds : (2539/100000:ℝ) < FifthActualIntegralRecovery.recovery ∧
    FifthActualIntegralRecovery.recovery < 9007/100000 := by
  have h : (2539/100000:ℝ) < lowerPayment ∧ upperPayment < 9007/100000 := by
    norm_num [lowerPayment,upperPayment,lowerQuad,lowerLin,upperQuad,upperLin,dLower,dUpper,
      cap,hi,lo,f0,slope,JointLogTotalComparison.V,lowerLog,upperLog,fifthDensity,
      FifthClassicalShape.k,FifthClassicalShape.c,FifthClassicalShape.f,FifthClassicalShape.q,
      s0,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  exact ⟨h.1.trans_le recovery_enclosure.1,recovery_enclosure.2.trans_lt h.2⟩

/-- The fixed Base curvature gain and full fifth recovery are charged once. -/
def coefficient : ℝ := JointSixthFourDiagnostic.coefficient+
  FifthActualIntegralRecovery.recovery/4+68650/47545083

theorem coefficient_le_actual : coefficient ≤ JointHMotherPayment.unroundedCoefficient := by
  have hgap := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at hgap
  have hs := AnalyticTotalThreshold.signed_losses_nonnegative
  have hj := JointJLossStrength.actual_jLoss_lower
  have h6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.1
  have h4 := FourActualCapRecovery.actual_fourLoss_lower
  have h5 := FifthActualIntegralRecovery.fifth_loss_localization.1
  have hb := BaseGSharedActualRecovery.shared_recovery
  rw [BaseGSharedActualRecovery.recovery_exact] at hb
  unfold coefficient JointSixthFourDiagnostic.coefficient ClassicalLossBottleneck.recoveredCoefficient
  unfold AnalyticTotalThreshold.sixthLoss at hgap h6
  linarith only [hgap,hs.1,hs.2.1,hj,h6,h4,h5,hb]

theorem seven_error_identity : JointHMotherPayment.unroundedCoefficient-coefficient =
    (AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+
      (AnalyticTotalThreshold.jLoss-JointJLossStrength.recovery)+
      (AnalyticTotalThreshold.sharedLoss-274600/47545083)+
      (fifthPairFlin-FifthActualIntegralRecovery.logIntegral)+
      (truncatedSixthLowerF6lin-ClassicalLossBottleneck.sixthLogIntegral)+
      (AnalyticTotalThreshold.fourLoss-FourActualCapRecovery.recovery))/4 := by
  have h := FifthActualIntegralRecovery.seven_error_identity
  unfold coefficient FifthActualIntegralRecovery.coefficient at *
  linarith only [h]

/-- The exact target comparison is retained before any interval enclosure. -/
theorem target_exact_difference : AnalyticTotalThreshold.target-coefficient =
    JointLogTotalComparison.rationalDeficit-Phase18.g18-Phase20.psiPaymentLoss-
    JointLogTotalComparison.logRemainder-
    (JointJLossStrength.recovery-JointJLossStrength.fixedRecovery)/4-
    JointLogTotalComparison.targetSlack-
    TotalEndpointComparison.quad/4*(TotalEndpointComparison.D-FifthClassicalShape.ell)^2-
    (ClassicalLossBottleneck.sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint)/4-
    FourActualCapRecovery.recovery/4-FifthActualIntegralRecovery.recovery/4-68650/47545083 := by
  have h := SixthLogTotalMagnitude.recovered_exact_difference
  unfold coefficient JointSixthFourDiagnostic.coefficient
  linarith only [h]

/-- A substantial absolute payment, as opposed to a fraction of an unknown loss. -/
theorem combined_payment_bounds : (1/160:ℝ)+68650/47545083 <
    coefficient-JointSixthFourDiagnostic.coefficient ∧
    coefficient-JointSixthFourDiagnostic.coefficient < 901/40000+68650/47545083 := by
  unfold coefficient
  constructor <;> linarith only [recovery_magnitude.1,recovery_magnitude.2]

/-- Honest joint localization: this interval crosses zero and does not settle the target. -/
theorem total_target_localization : -(3/125:ℝ) < AnalyticTotalThreshold.target-coefficient ∧
    AnalyticTotalThreshold.target-coefficient < 7/50 := by
  have h1 := JointSixthFourDiagnostic.certificate_strictly_insufficient
  have h2 := SixthLogTotalMagnitude.recovered_deficit_bounds.2
  have hp := combined_payment_bounds
  have hf : (49/10000:ℝ) < FourActualCapRecovery.recovery/4 := by
    rw [FourActualCapRecovery.recovery_exact]
    norm_num
  have hshort := JointSixthFourDiagnostic.shortfall_positive
  unfold coefficient JointSixthFourDiagnostic.coefficient at hp
  unfold coefficient JointSixthFourDiagnostic.coefficient at h1 ⊢
  constructor <;> linarith only [h1,h2,hp.1,hp.2,hf,hshort]

end
end Wu2008DoubleSieve.FifthLogTotalMagnitude
