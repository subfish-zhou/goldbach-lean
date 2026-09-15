import MathlibNt.Wu2008DoubleSieve.ClassicalRemainingBounds

namespace Wu2008DoubleSieve.ClassicalLogFourBounds
open Real Set MeasureTheory FourRoughClosedMass
open scoped Interval

/-- FTC for every logarithmic tail power, including a collapsed interval. -/
theorem integral_log_tail {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    (∫ x in a..b, C*(log b-log x)^n/x) =
      C*(log b-log a)^(n+1)/(n+1) := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have hd (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun x => -C*(log b-log x)^(n+1)/(n+1))
        (C*(log b-log x)^n/x) x := by
    rw [uIcc_of_le hab] at hx
    have hx0 := ha.trans_le hx.1
    have h := ((((hasDerivAt_const x (log b)).sub
      (hasDerivAt_log hx0.ne')).pow (n+1)).const_mul (-C)).div_const (n+1)
    convert h using 1 <;> first | rfl | (simp; field_simp)
  have hi : IntervalIntegrable (fun x => C*(log b-log x)^n/x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hx : ∀ x ∈ uIcc a b, x ≠ 0 := by
      intro x hx; rw [uIcc_of_le hab] at hx; exact (ha.trans_le hx.1).ne'
    exact (continuousOn_const.mul ((continuousOn_const.sub
      (continuousOn_id.log hx)).pow n)).div continuousOn_id hx
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp only [sub_self, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_div, zero_sub]
  ring

theorem integral_le_log_tail {f : ℝ → ℝ} {a b C : ℝ} (hf : Continuous f)
    (ha : 0 < a) (hab : a ≤ b) (n : ℕ)
    (hb : ∀ x ∈ Icc a b, f x ≤ C*(log b-log x)^n/x) :
    (∫ x in a..b, f x) ≤ C*(log b-log a)^(n+1)/(n+1) := by
  rw [← integral_log_tail ha hab n]
  apply intervalIntegral.integral_mono_on hab (hf.intervalIntegrable a b) _ hb
  apply ContinuousOn.intervalIntegrable
  have hx : ∀ x ∈ uIcc a b, x ≠ 0 := by
    intro x hx; rw [uIcc_of_le hab] at hx; exact (ha.trans_le hx.1).ne'
  exact (continuousOn_const.mul ((continuousOn_const.sub
    (continuousOn_id.log hx)).pow n)).div continuousOn_id hx

noncomputable def densityCap : ℝ := 4/(7*alpha)
noncomputable def tailLog : ℝ := log beta-log alpha
noncomputable def crossLog : ℝ := log (lam-alpha)-log beta

/-- Only the extra y reciprocal is bounded by alpha; the product density is retained. -/
theorem regular_le_density {x y z t : ℝ}
    (hx : alpha ≤ x) (hy : alpha ≤ y) (hz : alpha ≤ z) (ht : alpha ≤ t) :
    regularKernel x y z t ≤ densityCap/(x*y*z*t) := by
  have ha := fixed_geometry.2.1
  have hx0 := ha.trans_le hx
  have hy0 := ha.trans_le hy
  have hz0 := ha.trans_le hz
  have ht0 := ha.trans_le ht
  have h := SecondFunctionalFourSevenths.buchstab_le_four_sevenths
    (show (7/4 : ℝ) ≤ max 2 (parameter x y z t) from
      le_trans (by norm_num) (le_max_left _ _))
  have he : regularKernel x y z t =
      LiLiuPrereqBuchstab.buchstab (max 2 (parameter x y z t))/(x*y^2*z*t) := by
    simp only [regularKernel, clip, max_eq_right hx, max_eq_right hy,
      max_eq_right hz, max_eq_right ht]
  rw [he]
  have hd : 0 < x*y^2*z*t := by positivity
  calc
    _ ≤ (4/7)/(x*y^2*z*t) := div_le_div_of_nonneg_right h hd.le
    _ = ((4/7)/y)/(x*y*z*t) := by field_simp
    _ ≤ ((4/7)/alpha)/(x*y*z*t) := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left (by norm_num) ha hy) (by positivity)
    _ = _ := by unfold densityCap; ring

theorem inner10_upper {x y z : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hz : alpha ≤ z) (hzb : z ≤ beta) :
    regularInner10 x y z ≤ densityCap/(x*y*z)*(log beta-log z) := by
  have h := integral_le_log_tail
    (C := densityCap/(x*y*z)) (f := fun t => regularKernel x y z t)
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hz) hzb 0 (fun t ht => by
      simpa only [pow_zero, mul_one, div_div] using
        regular_le_density hx hy hz (hz.trans ht.1))
  simpa [regularInner10] using h

theorem middle10_upper {x y : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y) (hyb : y ≤ beta) :
    regularMiddle10 x y ≤ densityCap/(2*x*y)*(log beta-log y)^2 := by
  have h := integral_le_log_tail
    (C := densityCap/(x*y)) (f := fun z => regularInner10 x y z)
    (regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hy) hyb 1 (fun z hz => by
      have hh := inner10_upper hx hy (hy.trans hz.1) hz.2
      convert hh using 1
      ring)
  change regularMiddle10 x y ≤ _ at h
  convert h using 1
  ring

theorem outer10_upper {x : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) :
    regularOuter10 x ≤ densityCap/(6*x)*(log beta-log x)^3 := by
  have h := integral_le_log_tail
    (C := densityCap/(2*x)) (f := fun y => regularMiddle10 x y)
    (regularMiddle10_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hx) hxb 2 (fun y hy => by
      have hh := middle10_upper hx (hx.trans hy.1) hy.2
      convert hh using 1
      ring)
  change regularOuter10 x ≤ _ at h
  convert h using 1
  ring

theorem I10_log_upper : I10 ≤ densityCap/24*tailLog^4 := by
  rw [I10_eq_regular]
  have h := integral_le_log_tail (C := densityCap/6) regularOuter10_continuous fixed_geometry.2.1
    fixed_geometry.2.2.1 3 (fun x hx => by
      have hh := outer10_upper hx.1 hx.2
      convert hh using 1
      ring)
  convert h using 1
  unfold tailLog
  ring

theorem inner11_upper {x y z : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hz : alpha ≤ z) (hzb : z ≤ beta) :
    regularInner11 x y z ≤ densityCap*crossLog/(x*y*z) := by
  have ha := fixed_geometry.2.1
  have hb : 0 < beta := ha.trans_le fixed_geometry.2.2.1
  have horder : beta ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  have h := integral_le_log_tail
    (C := densityCap/(x*y*z)) (f := fun t => regularKernel x y z t)
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    hb horder 0 (fun t ht => by
      simpa only [pow_zero, mul_one, div_div] using
        regular_le_density hx hy hz (fixed_geometry.2.2.1.trans ht.1))
  change regularInner11 x y z ≤ _ at h
  norm_num only [Nat.cast_zero, zero_add, pow_one, div_one] at h
  have hl : log (lam-z) ≤ log (lam-alpha) :=
    log_le_log (hb.trans_le horder) (by linarith)
  have hd : 0 ≤ densityCap/(x*y*z) := by
    have hx0 := ha.trans_le hx
    have hy0 := ha.trans_le hy
    have hz0 := ha.trans_le hz
    unfold densityCap
    positivity
  unfold crossLog
  calc
    _ ≤ densityCap/(x*y*z)*(log (lam-z)-log beta) := h
    _ ≤ densityCap/(x*y*z)*(log (lam-alpha)-log beta) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hl _) hd
    _ = _ := by ring

theorem middle11_upper {x y : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y) (hyb : y ≤ beta) :
    regularMiddle11 x y ≤ densityCap*crossLog/(x*y)*(log beta-log y) := by
  have h := integral_le_log_tail
    (C := densityCap*crossLog/(x*y)) (f := fun z => regularInner11 x y z)
    (regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hy) hyb 0 (fun z hz => by
      have hh := inner11_upper hx hy (hy.trans hz.1) hz.2
      convert hh using 1
      ring)
  simpa [regularMiddle11] using h

theorem outer11_upper {x : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) :
    regularOuter11 x ≤ densityCap*crossLog/(2*x)*(log beta-log x)^2 := by
  have h := integral_le_log_tail
    (C := densityCap*crossLog/x) (f := fun y => regularMiddle11 x y)
    (regularMiddle11_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop))
    (fixed_geometry.2.1.trans_le hx) hxb 1 (fun y hy => by
      have hh := middle11_upper hx (hx.trans hy.1) hy.2
      convert hh using 1
      ring)
  change regularOuter11 x ≤ _ at h
  convert h using 1
  ring

theorem I11_log_upper : I11 ≤ densityCap*crossLog/6*tailLog^3 := by
  rw [I11_eq_regular]
  have h := integral_le_log_tail (C := densityCap*crossLog/2) regularOuter11_continuous fixed_geometry.2.1
    fixed_geometry.2.2.1 2 (fun x hx => by
      have hh := outer11_upper hx.1 hx.2
      convert hh using 1
      ring)
  convert h using 1
  unfold tailLog
  ring

theorem log_caps : 0 ≤ tailLog ∧ tailLog ≤ 1/2 ∧ 0 ≤ crossLog ∧ crossLog ≤ 1 := by
  have ha := fixed_geometry.2.1
  have hab := fixed_geometry.2.2.1
  have hb := ha.trans_le hab
  have hbc : beta ≤ lam-alpha := by
    norm_num [alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]
  have hl := SecondFunctionalFourSevenths.log_chord_bound ha hab
  have hu := SecondFunctionalFourSevenths.log_chord_bound hb hbc
  rw [log_div hb.ne' ha.ne'] at hl
  rw [log_div (hb.trans_le hbc).ne' hb.ne'] at hu
  have hl0 := log_le_log ha hab
  have hu0 := log_le_log hb hbc
  change log beta-log alpha ≤ _ at hl
  change log (lam-alpha)-log beta ≤ _ at hu
  change 0 ≤ log beta-log alpha ∧ log beta-log alpha ≤ 1/2 ∧
    0 ≤ log (lam-alpha)-log beta ∧ log (lam-alpha)-log beta ≤ 1
  norm_num [alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda] at hl hu
  refine ⟨sub_nonneg.mpr hl0, ?_, sub_nonneg.mpr hu0, ?_⟩ <;>
    norm_num [alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda] <;>
    linarith

/-- The original fourfold integrals, including the moving I11 upper endpoint. -/
theorem four_weighted_lt_two : 8*I10+8*I11 < 2 := by
  obtain ⟨hl0, hl, hu0, hu⟩ := log_caps
  have h10 := I10_log_upper
  have h11 := I11_log_upper
  have h3 := pow_le_pow_left₀ hl0 hl 3
  have h4 := pow_le_pow_left₀ hl0 hl 4
  have hprod := mul_le_mul hu h3 (pow_nonneg hl0 _) (by norm_num : (0 : ℝ) ≤ 1)
  norm_num only [densityCap,alpha,truncatedSixthLowerAlpha] at h10 h11
  nlinarith

end Wu2008DoubleSieve.ClassicalLogFourBounds
