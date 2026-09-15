import EJointPolynomials
noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve SharpLogRecurrence Wu08OriginalFirstSteps
open scoped Interval
namespace EJoint

theorem shifted_integral {F f : ℝ → ℝ}
    (hd : ∀ t : ℝ, HasDerivAt F (f t) t) (hc : Continuous f)
    (hz : F 0 = 0) (c b : ℝ) :
    (∫ u in c..b, f (u-c)) = F (b-c) := by
  have h (u : ℝ) : HasDerivAt (fun u : ℝ => F (u-c)) (f (u-c)) u := by
    convert (hd (u-c)).comp u ((hasDerivAt_id u).sub_const c) using 1 <;> first | rfl | simp
  have hcont : Continuous (fun u : ℝ => f (u-c)) := hc.comp (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => h u)
    (hcont.intervalIntegrable c b)]
  simp [hz]

theorem weighted_integral {F G f g : ℝ → ℝ}
    (hF : ∀ t : ℝ, HasDerivAt F (f t) t)
    (hG : ∀ t : ℝ, HasDerivAt G (g t) t)
    (hf : Continuous f) (hg : Continuous g)
    (hzF : F 0 = 0) (hzG : G 0 = 0) (a d c b : ℝ) :
    (∫ u in c..b, 2*a*f (u-c)-a^2*d*g (u-c)) =
      2*a*F (b-c)-a^2*d*G (b-c) := by
  have hf' : Continuous (fun u : ℝ => 2*a*f (u-c)) :=
    (hf.comp (by fun_prop)).const_mul (2*a)
  have hg' : Continuous (fun u : ℝ => a^2*d*g (u-c)) :=
    (hg.comp (by fun_prop)).const_mul (a^2*d)
  rw [intervalIntegral.integral_sub (hf'.intervalIntegrable c b)
    (hg'.intervalIntegrable c b), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, shifted_integral hF hf hzF,
    shifted_integral hG hg hzG]

theorem square_certificate {n q : ℝ} (hn : 0 ≤ n) (hq : 0 < q) (a : ℝ) :
    n*(2*a-a^2*q) ≤ n/q := by
  apply (le_div_iff₀ hq).2
  have h := mul_nonneg hn (sq_nonneg (1-a*q))
  nlinarith only [h]

theorem lowerLog_kernel {u : ℝ} (hu : 2 ≤ u) :
    A0 (u-2)/(3*u^4) ≤ k u := by
  have hu0 : 0 < u := by linarith
  have h := div_le_div_of_nonneg_right (log_lower (by linarith : 1 ≤ u-1)) hu0.le
  rw [k_literal hu]
  convert h using 1 <;> first | rfl | skip
  unfold lowerLog A0
  rw [show u-1+1=u by ring]
  field_simp
  ring

theorem joint_kernel (a d : ℝ) {u : ℝ} (hu : 2 ≤ u) (hd : 0 < d) :
    d*(2*a*A0 (u-2)-a^2*d*B0 (u-2)) ≤ k u := by
  have hu0 : 0 < u := by linarith
  have hn := numerator_nonneg (by linarith : 0 ≤ u-2)
  have hq : 0 < 3*u^4*d := by positivity
  have h := mul_le_mul_of_nonneg_left (square_certificate hn hq a) hd.le
  have he1 : d*(A0 (u-2)*(2*a-a^2*(3*u^4*d))) =
      d*(2*a*A0 (u-2)-a^2*d*B0 (u-2)) := by
    rw [denominator_kernel]
    ring
  have he2 : d*(A0 (u-2)/(3*u^4*d)) = A0 (u-2)/(3*u^4) := by
    field_simp
  rw [he1,he2] at h
  exact h.trans (lowerLog_kernel hu)

end EJoint
