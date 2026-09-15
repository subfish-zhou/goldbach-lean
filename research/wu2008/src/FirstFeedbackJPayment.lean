import FirstFeedbackJKernel

namespace FirstFeedbackIntegrals
open Wu2008DoubleSieve NodeExtension ActualNineFeedback Real Set MeasureTheory
open Wu04WholeCollection SharpLogRecurrence
open scoped Interval BigOperators
noncomputable section

def jPaid (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  (aProfile (nineProfile z)+tailCells z (S-2))*jWeight s S+z 0*jCurvePaid s S

/-- The original J is paid in full, including its first-cell logarithmic tail. -/
theorem jPaid_le {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3<S) (hS5 : S≤5) (hsS : s≤S)
    (hr : 2≤S-S/s) (hS2 : S-2≤upperNode 0) : jPaid z s S≤profileJ z s S := by
  have hg := J_geometry hs hS.le hS5 hsS hr
  have hA := (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).1
  have ht := tailCells_paid hz (by linarith : 1≤S-2) hS2
  have ht0 := tailCells_nonneg hz (by linarith : 1≤S-2) hS2
  have hi : IntervalIntegrable (fun u : ℝ => 1/(u*(1-u))) volume (1-1/s) (1-1/S) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hg.1)
    intro u hu
    have h := hg.2 u hu
    have hu0 := h.1
    have hu1 : 0<1-u := by linarith [h.2.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hj := jCurve_integrable hs hS hS5 hsS hr
  have hm := intervalIntegral.integral_mono_on hg.1
    ((hi.const_mul (aProfile (nineProfile z)+tailCells z (S-2))).add (hj.const_mul (z 0)))
    (profileJ_integrable z hs hS.le hS5 hsS hr) (fun u hu => by
      have h := hg.2 u hu
      have hSu : S*u≤S-1 := by
        have hmul := mul_le_mul_of_nonneg_left hu.2 (by linarith : 0≤S)
        have he : S*(1-1/S)=S-1 := by field_simp
        rw [he] at hmul
        exact hmul
      have harg : 1 ≤ (S-2)/(S*u-1) :=
        (one_le_div (by linarith only [h.2.2.1] : 0<S*u-1)).mpr (by linarith only [hSu])
      have hlog := log_lower harg
      have hzlog := mul_le_mul_of_nonneg_left hlog (hz 0)
      have hn : aProfile (nineProfile z)+tailCells z (S-2)+
          z 0*lowerLog ((S-2)/(S*u-1)) ≤ gProfile (nineProfile z) (S*u) := by
        rw [g_first_cell z h.2.2.1 hSu hS2]
        linarith only [ht,hzlog]
      have hdiv := div_le_div_of_nonneg_right hn
        (mul_nonneg h.1.le (by linarith [h.2.1] : 0≤1-u))
      convert hdiv using 1 <;> first | rfl | skip
      unfold jCurveDensity
      ring)
  rw [intervalIntegral.integral_add (hi.const_mul _) (hj.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    weight_integral hs hS.le hS5 hsS hr] at hm
  have hw := mul_le_mul_of_nonneg_left
    (bounds (div_pos (by linarith : 0<S-1) (by linarith : 0<s-1))).1 (add_nonneg hA ht0)
  have hc := mul_le_mul_of_nonneg_left (jCurvePaid_le_integral hs hS hS5 hsS hr) (hz 0)
  change _ ≤ profileJ z s S at hm
  unfold jPaid jWeight
  linarith only [hm,hw,hc]

def firstACoefficient (s S : ℝ) : ℝ := low (4/(S-1))+jWeight s S/2

def firstResidual (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  eCells z S+(tailCells z (S-2)*jWeight s S+z 0*jCurvePaid s S)/2

/-- All original first-feedback terms survive; only their genuine common aProfile remains analytic. -/
theorem firstFeedback_affine_lower {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3<S) (hS5 : S≤5) (hsS : s≤S)
    (hr : 2≤S-S/s) (hS2 : S-2≤upperNode 0) :
    firstACoefficient s S*aProfile (nineProfile z)+firstResidual z s S≤firstFeedback z s S := by
  have hj := jPaid_le hz hs hS hS5 hsS hr hS2
  have he := eCells_paid hz hS.le hS2
  have hA := (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).1
  have hw := mul_le_mul_of_nonneg_right (bounds (div_pos (by norm_num : (0:ℝ)<4)
    (by linarith : 0<S-1))).1 hA
  unfold firstFeedback firstACoefficient firstResidual jPaid at *
  nlinarith only [hj,he,hw]

end
end FirstFeedbackIntegrals
