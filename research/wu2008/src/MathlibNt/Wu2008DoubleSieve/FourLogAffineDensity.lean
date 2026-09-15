import MathlibNt.Wu2008DoubleSieve.ClassicalLogFourBounds

namespace Wu2008DoubleSieve.FourLogAffine
open Real Set MeasureTheory FourRoughClosedMass ClassicalLogFourBounds
open scoped Interval

/-- A universal log-affine reciprocal upper envelope, not a log lower bound. -/
theorem reciprocal_log_affine {a b y : ℝ} (ha : 0 < a) (hay : a ≤ y)
    (hyb : y ≤ b) : 1/y ≤ 1/a-log (y/a)/b := by
  have hy := ha.trans_le hay
  have hb := hy.trans_le hyb
  have hl : log (y/a) ≤ (y-a)/a := by
    convert log_le_sub_one_of_pos (div_pos hy ha) using 1
    field_simp
  have hs : 1/y ≤ 1/a-(y-a)/(a*b) := by
    have hid : 1/a-(y-a)/(a*b)-1/y = (y-a)*(b-y)/(a*b*y) := by
      field_simp
      ring
    have hn : 0 ≤ (y-a)*(b-y)/(a*b*y) :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hay) (sub_nonneg.mpr hyb)) (by positivity)
    linarith
  have hh : log (y/a)/b ≤ (y-a)/(a*b) := by
    calc
      _ ≤ ((y-a)/a)/b := div_le_div_of_nonneg_right hl hb.le
      _ = _ := by ring
  linarith

noncomputable def C0 : ℝ := 1/alpha-tailLog/beta
noncomputable def ell (y : ℝ) : ℝ := log beta-log y
noncomputable def affine (y : ℝ) : ℝ := C0+ell y/beta

/-- At the endpoint the same reciprocal inequality proves strict positivity. -/
theorem C0_lower : 1/beta ≤ C0 := by
  have ha := fixed_geometry.2.1
  have hb := ha.trans_le fixed_geometry.2.2.1
  have h := reciprocal_log_affine ha fixed_geometry.2.2.1 (le_refl beta)
  rw [log_div hb.ne' ha.ne'] at h
  exact h

theorem C0_pos : 0 < C0 :=
  lt_of_lt_of_le (one_div_pos.mpr (fixed_geometry.2.1.trans_le fixed_geometry.2.2.1)) C0_lower

theorem ell_nonneg {y : ℝ} (hy : alpha ≤ y) (hyb : y ≤ beta) : 0 ≤ ell y :=
  sub_nonneg.mpr (log_le_log (fixed_geometry.2.1.trans_le hy) hyb)

theorem affine_pos {y : ℝ} (hy : alpha ≤ y) (hyb : y ≤ beta) : 0 < affine y := by
  have hb := fixed_geometry.2.1.trans_le fixed_geometry.2.2.1
  exact add_pos_of_pos_of_nonneg C0_pos (div_nonneg (ell_nonneg hy hyb) hb.le)

theorem affine_eq {y : ℝ} (hy : alpha ≤ y) : affine y = 1/alpha-log (y/alpha)/beta := by
  rw [log_div (fixed_geometry.2.1.trans_le hy).ne' fixed_geometry.2.1.ne']
  unfold affine C0 ell tailLog
  ring

theorem reciprocal_le_affine {y : ℝ} (hy : alpha ≤ y) (hyb : y ≤ beta) :
    1/y ≤ affine y := by
  rw [affine_eq hy]
  exact reciprocal_log_affine fixed_geometry.2.1 hy hyb

theorem affine_le_old {y : ℝ} (hy : alpha ≤ y) : affine y ≤ 1/alpha := by
  rw [affine_eq hy, log_div (fixed_geometry.2.1.trans_le hy).ne' fixed_geometry.2.1.ne']
  have h := div_nonneg (sub_nonneg.mpr (log_le_log fixed_geometry.2.1 hy))
    (fixed_geometry.2.1.trans_le fixed_geometry.2.2.1).le
  linarith

/-- The original squared y denominator is retained before its extra reciprocal is bounded. -/
theorem regular_le_affine {x y z t : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hyb : y ≤ beta) (hz : alpha ≤ z) (ht : alpha ≤ t) :
    regularKernel x y z t ≤ (4/7)*affine y/(x*y*z*t) := by
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
  calc
    _ ≤ (4/7)/(x*y^2*z*t) := div_le_div_of_nonneg_right h (by positivity)
    _ = ((4/7)*(1/y))/(x*y*z*t) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (reciprocal_le_affine hy hyb) (by norm_num)) (by positivity)

/-- Continuous logarithmic tails supply real interval integrability. -/
theorem tail_integrable {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    IntervalIntegrable (fun x => C*(log b-log x)^n/x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hx : ∀ x ∈ uIcc a b, x ≠ 0 := by
    intro x hx; rw [uIcc_of_le hab] at hx; exact (ha.trans_le hx.1).ne'
  exact (continuousOn_const.mul ((continuousOn_const.sub
    (continuousOn_id.log hx)).pow n)).div continuousOn_id hx

/-- Two real FTC evaluations, joined by integral_add; valid for arbitrary signed constants. -/
theorem integral_two_tails {a b C D : ℝ} (ha : 0 < a) (hab : a ≤ b) (n m : ℕ) :
    (∫ x in a..b, (C*(log b-log x)^n/x+D*(log b-log x)^m/x)) =
      C*(log b-log a)^(n+1)/(n+1)+D*(log b-log a)^(m+1)/(m+1) := by
  rw [intervalIntegral.integral_add (tail_integrable ha hab n) (tail_integrable ha hab m),
    integral_log_tail ha hab n, integral_log_tail ha hab m]

theorem integral_le_two_tails {f : ℝ → ℝ} {a b C D : ℝ} (hf : Continuous f)
    (ha : 0 < a) (hab : a ≤ b) (n m : ℕ)
    (hb : ∀ x ∈ Icc a b, f x ≤ C*(log b-log x)^n/x+D*(log b-log x)^m/x) :
    (∫ x in a..b, f x) ≤
      C*(log b-log a)^(n+1)/(n+1)+D*(log b-log a)^(m+1)/(m+1) := by
  rw [← integral_two_tails ha hab n m]
  exact intervalIntegral.integral_mono_on hab (hf.intervalIntegrable a b)
    ((tail_integrable ha hab n).add (tail_integrable ha hab m)) hb

end Wu2008DoubleSieve.FourLogAffine
