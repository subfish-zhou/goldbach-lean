import MathlibNt.Wu2008DoubleSieve.JCubicExactEnvelope

namespace Wu2008DoubleSieve.FourPositiveLogLower
open Real Set MeasureTheory FourRoughClosedMass
open scoped Interval

/-- Reuse the exact all-power FTC, with genuine integrability on both sides. -/
theorem log_tail_le_integral {f : ℝ → ℝ} {a b C : ℝ} (hf : Continuous f)
    (ha : 0 < a) (hab : a ≤ b) (n : ℕ)
    (hb : ∀ x ∈ Icc a b, C*(log b-log x)^n/x ≤ f x) :
    C*(log b-log a)^(n+1)/(n+1) ≤ (∫ x in a..b, f x) := by
  rw [← ClassicalLogFourBounds.integral_log_tail ha hab n]
  apply intervalIntegral.integral_mono_on hab _ (hf.intervalIntegrable a b) hb
  apply ContinuousOn.intervalIntegrable
  have hx : ∀ x ∈ uIcc a b, x ≠ 0 := by
    intro x hx; rw [uIcc_of_le hab] at hx; exact (ha.trans_le hx.1).ne'
  exact (continuousOn_const.mul ((continuousOn_const.sub
    (continuousOn_id.log hx)).pow n)).div continuousOn_id hx

noncomputable def densityLower : ℝ := 1/(2*beta)
noncomputable def tailLog : ℝ := log beta-log alpha
noncomputable def crossLog : ℝ := log (lam-beta)-log beta

/-- Pay the extra y reciprocal by 1/beta, retaining the four-coordinate density. -/
theorem density_le_regular {x y z t : ℝ}
    (hx : alpha ≤ x) (hy : alpha ≤ y) (hyb : y ≤ beta)
    (hz : alpha ≤ z) (ht : alpha ≤ t) :
    densityLower/(x*y*z*t) ≤ regularKernel x y z t := by
  have ha := fixed_geometry.2.1
  have hb := ha.trans_le fixed_geometry.2.2.1
  have hx0 := ha.trans_le hx
  have hy0 := ha.trans_le hy
  have hz0 := ha.trans_le hz
  have ht0 := ha.trans_le ht
  have h := LiLiuPrereqBuchstab.one_half_le_buchstab
    (show (1 : ℝ) ≤ max 2 (parameter x y z t) from
      le_trans (by norm_num) (le_max_left _ _))
  have he : regularKernel x y z t =
      LiLiuPrereqBuchstab.buchstab (max 2 (parameter x y z t))/(x*y^2*z*t) := by
    simp only [regularKernel, clip, max_eq_right hx, max_eq_right hy,
      max_eq_right hz, max_eq_right ht]
  rw [he]
  calc
    _ = ((1/2)/beta)/(x*y*z*t) := by unfold densityLower; ring
    _ ≤ ((1/2)/y)/(x*y*z*t) := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left (by norm_num) hy0 hyb) (by positivity)
    _ = (1/2)/(x*y^2*z*t) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right h (by positivity)

/-- Literal original kernel comparison on the original ten window. -/
theorem density_le_kernel_ten {x y z t : ℝ}
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzt : z ≤ t) (ht : t ≤ beta) :
    1/(2*beta*x*y*z*t) ≤ kernel x y z t := by
  rw [← regularKernel_eq_ten hx hxy hyz hzt ht]
  have h := density_le_regular hx (hx.trans hxy) (hyz.trans (hzt.trans ht))
    (hx.trans (hxy.trans hyz)) (hx.trans (hxy.trans (hyz.trans hzt)))
  simpa only [densityLower, div_div, mul_assoc] using h

/-- Literal original kernel comparison on the original eleven window. -/
theorem density_le_kernel_eleven {x y z t : ℝ}
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ beta)
    (hbt : beta ≤ t) (ht : t ≤ lam-z) :
    1/(2*beta*x*y*z*t) ≤ kernel x y z t := by
  rw [← regularKernel_eq_eleven hx hxy hyz hz hbt ht]
  have h := density_le_regular hx (hx.trans hxy) (hyz.trans hz)
    (hx.trans (hxy.trans hyz)) (fixed_geometry.2.2.1.trans hbt)
  simpa only [densityLower, div_div, mul_assoc] using h

theorem inner10_lower {x y z : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hyb : y ≤ beta) (hz : alpha ≤ z) (hzb : z ≤ beta) :
    densityLower/(x*y*z)*(log beta-log z) ≤ regularInner10 x y z := by
  have h := log_tail_le_integral
    (C := densityLower/(x*y*z)) (f := fun t => regularKernel x y z t)
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hz) hzb 0 (fun t ht => by
      simpa only [pow_zero, mul_one, div_div] using
        density_le_regular hx hy hyb hz (hz.trans ht.1))
  simpa [regularInner10] using h

theorem middle10_lower {x y : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y) (hyb : y ≤ beta) :
    densityLower/(2*x*y)*(log beta-log y)^2 ≤ regularMiddle10 x y := by
  have h := log_tail_le_integral
    (C := densityLower/(x*y)) (f := fun z => regularInner10 x y z)
    (regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hy) hyb 1 (fun z hz => by
      have hh := inner10_lower hx hy hyb (hy.trans hz.1) hz.2
      convert hh using 1
      ring)
  change _ ≤ regularMiddle10 x y at h
  convert h using 1
  ring

theorem outer10_lower {x : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) :
    densityLower/(6*x)*(log beta-log x)^3 ≤ regularOuter10 x := by
  have h := log_tail_le_integral
    (C := densityLower/(2*x)) (f := fun y => regularMiddle10 x y)
    (regularMiddle10_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hx) hxb 2 (fun y hy => by
      have hh := middle10_lower hx (hx.trans hy.1) hy.2
      convert hh using 1
      ring)
  change _ ≤ regularOuter10 x at h
  convert h using 1
  ring

theorem I10_log_lower : tailLog^4/(48*beta) ≤ I10 := by
  rw [I10_eq_regular]
  have h := log_tail_le_integral (C := densityLower/6) regularOuter10_continuous fixed_geometry.2.1
    fixed_geometry.2.2.1 3 (fun x hx => by
      have hh := outer10_lower hx.1 hx.2
      convert hh using 1
      ring)
  convert h using 1
  unfold tailLog densityLower
  ring

theorem inner11_lower {x y z : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hyb : y ≤ beta) (hz : alpha ≤ z) (hzb : z ≤ beta) :
    densityLower*crossLog/(x*y*z) ≤ regularInner11 x y z := by
  have ha := fixed_geometry.2.1
  have hb : 0 < beta := ha.trans_le fixed_geometry.2.2.1
  have horder : beta ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  have hbase : beta ≤ lam-beta := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  have h := log_tail_le_integral
    (C := densityLower/(x*y*z)) (f := fun t => regularKernel x y z t)
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    hb horder 0 (fun t ht => by
      simpa only [pow_zero, mul_one, div_div] using
        density_le_regular hx hy hyb hz (fixed_geometry.2.2.1.trans ht.1))
  change _ ≤ regularInner11 x y z at h
  norm_num only [Nat.cast_zero, zero_add, pow_one, div_one] at h
  have hl : log (lam-beta) ≤ log (lam-z) :=
    log_le_log (hb.trans_le hbase) (by linarith)
  have hd : 0 ≤ densityLower/(x*y*z) := by
    have hx0 := ha.trans_le hx
    have hy0 := ha.trans_le hy
    have hz0 := ha.trans_le hz
    unfold densityLower
    positivity
  unfold crossLog
  calc
    _ = densityLower/(x*y*z)*(log (lam-beta)-log beta) := by ring
    _ ≤ densityLower/(x*y*z)*(log (lam-z)-log beta) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hl _) hd
    _ ≤ _ := h

theorem middle11_lower {x y : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y) (hyb : y ≤ beta) :
    densityLower*crossLog/(x*y)*(log beta-log y) ≤ regularMiddle11 x y := by
  have h := log_tail_le_integral
    (C := densityLower*crossLog/(x*y)) (f := fun z => regularInner11 x y z)
    (regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hy) hyb 0 (fun z hz => by
      have hh := inner11_lower hx hy hyb (hy.trans hz.1) hz.2
      convert hh using 1
      ring)
  simpa [regularMiddle11] using h

theorem outer11_lower {x : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) :
    densityLower*crossLog/(2*x)*(log beta-log x)^2 ≤ regularOuter11 x := by
  have h := log_tail_le_integral
    (C := densityLower*crossLog/x) (f := fun y => regularMiddle11 x y)
    (regularMiddle11_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hx) hxb 1 (fun y hy => by
      have hh := middle11_lower hx (hx.trans hy.1) hy.2
      convert hh using 1
      ring)
  change _ ≤ regularOuter11 x at h
  convert h using 1
  ring

theorem I11_log_lower : crossLog*tailLog^3/(12*beta) ≤ I11 := by
  rw [I11_eq_regular]
  have h := log_tail_le_integral (C := densityLower*crossLog/2) regularOuter11_continuous fixed_geometry.2.1
    fixed_geometry.2.2.1 2 (fun x hx => by
      have hh := outer11_lower hx.1 hx.2
      convert hh using 1
      ring)
  convert h using 1
  unfold tailLog densityLower
  ring

end Wu2008DoubleSieve.FourPositiveLogLower
