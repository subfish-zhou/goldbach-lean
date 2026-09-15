import MathlibNt.Wu2008DoubleSieve.FourLogAffineDensity

namespace Wu2008DoubleSieve.FourLogAffine
open Real Set MeasureTheory FourRoughClosedMass ClassicalLogFourBounds
open scoped Interval

/-- The original t interval, including equality of its endpoints. -/
theorem inner10_upper {x y z : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hyb : y ≤ beta) (hz : alpha ≤ z) (hzb : z ≤ beta) :
    regularInner10 x y z ≤ (4/7)*affine y/(x*y*z)*ell z := by
  have h := integral_le_log_tail (f := fun t => regularKernel x y z t) (C := (4/7)*affine y/(x*y*z))
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hz) hzb 0 (fun t ht => by
      simpa only [pow_zero, mul_one, div_div] using
        regular_le_affine hx hy hyb hz (hz.trans ht.1))
  simpa [regularInner10, ell] using h

/-- The z FTC retains the affine y factor, including its extra tail power. -/
theorem middle10_upper {x y : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y) (hyb : y ≤ beta) :
    regularMiddle10 x y ≤ (4/7)*(C0*ell y^2/2+ell y^3/(2*beta))/(x*y) := by
  have h := integral_le_log_tail (f := fun z => regularInner10 x y z) (C := (4/7)*affine y/(x*y))
    (regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hy) hyb 1 (fun z hz => by
      have hh := inner10_upper hx hy hyb (hy.trans hz.1) hz.2
      convert hh using 1
      unfold ell
      ring)
  change regularMiddle10 x y ≤ _ at h
  convert h using 1
  unfold affine ell
  ring

theorem outer10_upper {x : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) :
    regularOuter10 x ≤ (4/7)*(C0*ell x^3/6+ell x^4/(8*beta))/x := by
  have h := integral_le_two_tails (f := fun y => regularMiddle10 x y) (C := (4/7)*C0/(2*x)) (D := (4/7)/(2*beta*x))
    (regularMiddle10_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hx) hxb 2 3 (fun y hy => by
      have hh := middle10_upper hx (hx.trans hy.1) hy.2
      convert hh using 1
      unfold ell
      ring)
  change regularOuter10 x ≤ _ at h
  convert h using 1
  unfold ell
  ring

/-- Four successive real FTC comparisons reconnect to the unmodified original I10. -/
theorem I10_log_affine_upper :
    I10 ≤ (4/7)*(tailLog^4/(24*alpha)-tailLog^5/(60*beta)) := by
  rw [I10_eq_regular]
  have h := integral_le_two_tails (C := (4/7)*C0/6) (D := (4/7)/(8*beta))
    regularOuter10_continuous fixed_geometry.2.1 fixed_geometry.2.2.1 3 4 (fun x hx => by
      have hh := outer10_upper hx.1 hx.2
      convert hh using 1
      unfold ell
      ring)
  convert h using 1
  unfold C0 tailLog
  ring

/-- First integrate up to the genuine lam-z, only then bound its logarithm. -/
theorem inner11_upper {x y z : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hyb : y ≤ beta) (hz : alpha ≤ z) (hzb : z ≤ beta) :
    regularInner11 x y z ≤ (4/7)*affine y*crossLog/(x*y*z) := by
  have ha := fixed_geometry.2.1
  have hb := ha.trans_le fixed_geometry.2.2.1
  have horder : beta ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  have h := integral_le_log_tail (f := fun t => regularKernel x y z t) (C := (4/7)*affine y/(x*y*z))
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    hb horder 0 (fun t ht => by
      simpa only [pow_zero, mul_one, div_div] using
        regular_le_affine hx hy hyb hz (fixed_geometry.2.2.1.trans ht.1))
  change regularInner11 x y z ≤ _ at h
  norm_num only [Nat.cast_zero, zero_add, pow_one, div_one] at h
  have hl : log (lam-z) ≤ log (lam-alpha) :=
    log_le_log (hb.trans_le horder) (by linarith)
  have hd : 0 ≤ (4/7)*affine y/(x*y*z) := by
    have hx0 := ha.trans_le hx
    have hy0 := ha.trans_le hy
    have hz0 := ha.trans_le hz
    have hp := affine_pos hy hyb
    positivity
  calc
    _ ≤ (4/7)*affine y/(x*y*z)*(log (lam-z)-log beta) := h
    _ ≤ (4/7)*affine y/(x*y*z)*(log (lam-alpha)-log beta) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hl _) hd
    _ = _ := by unfold crossLog; ring

theorem middle11_upper {x y : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y) (hyb : y ≤ beta) :
    regularMiddle11 x y ≤ (4/7)*crossLog*(C0*ell y+ell y^2/beta)/(x*y) := by
  have h := integral_le_log_tail (f := fun z => regularInner11 x y z) (C := (4/7)*affine y*crossLog/(x*y))
    (regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hy) hyb 0 (fun z hz => by
      have hh := inner11_upper hx hy hyb (hy.trans hz.1) hz.2
      convert hh using 1
      ring)
  change regularMiddle11 x y ≤ _ at h
  convert h using 1
  unfold affine ell
  ring

theorem outer11_upper {x : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) :
    regularOuter11 x ≤ (4/7)*crossLog*(C0*ell x^2/2+ell x^3/(3*beta))/x := by
  have h := integral_le_two_tails (f := fun y => regularMiddle11 x y) (C := (4/7)*crossLog*C0/x) (D := (4/7)*crossLog/(beta*x))
    (regularMiddle11_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hx) hxb 1 2 (fun y hy => by
      have hh := middle11_upper hx (hx.trans hy.1) hy.2
      convert hh using 1
      unfold ell
      ring)
  change regularOuter11 x ≤ _ at h
  convert h using 1
  unfold ell
  ring

/-- No enlargement of a moving integration domain and no additional outer factor four. -/
theorem I11_log_affine_upper :
    I11 ≤ (4/7)*crossLog*(tailLog^3/(6*alpha)-tailLog^4/(12*beta)) := by
  rw [I11_eq_regular]
  have h := integral_le_two_tails (C := (4/7)*crossLog*C0/2) (D := (4/7)*crossLog/(3*beta))
    regularOuter11_continuous fixed_geometry.2.1 fixed_geometry.2.2.1 2 3 (fun x hx => by
      have hh := outer11_upper hx.1 hx.2
      convert hh using 1
      unfold ell
      ring)
  convert h using 1
  unfold C0 tailLog
  ring

/-- This positive decomposition is required before paying the upper cross logarithm. -/
theorem eleven_bracket_nonneg : 0 ≤ tailLog^3/(6*alpha)-tailLog^4/(12*beta) := by
  have he : tailLog^3/(6*alpha)-tailLog^4/(12*beta) =
      C0*tailLog^3/6+tailLog^4/(12*beta) := by unfold C0; ring
  rw [he]
  have hL := log_caps.1
  have ha := fixed_geometry.2.1
  have hb := ha.trans_le fixed_geometry.2.2.1
  have hc := C0_pos
  positivity

end Wu2008DoubleSieve.FourLogAffine
