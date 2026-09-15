import EJointCalculus
noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve SharpLogRecurrence Wu08OriginalFirstSteps
open scoped Interval
namespace EJoint

theorem B_joint (a d : ℝ) (hd : 0 < d) {s : ℝ} (hs : 3 ≤ s) :
    d*(2*a*A1 (s-3)-a^2*d*B1 (s-3)) ≤ B s := by
  have hc : Continuous (fun u : ℝ => d*(2*a*A0 (u-2)-a^2*d*B0 (u-2))) := by
    unfold A0 B0
    fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : (2:ℝ) ≤ s-1)
    (hc.intervalIntegrable 2 (s-1)) (k_continuous.intervalIntegrable 2 (s-1))
    (fun u hu => joint_kernel a d hu.1 hd)
  rw [intervalIntegral.integral_const_mul,
    weighted_integral A1_deriv B1_deriv A0_continuous B0_continuous A1_zero B1_zero] at h
  rw [show s-1-2=s-3 by ring] at h
  exact h

theorem C_joint (a d : ℝ) (hd : 0 < d) {s : ℝ} (hs : 4 ≤ s) :
    d*(2*a*A2 (s-4)-a^2*d*B2 (s-4)) ≤ C s := by
  have hh (u : ℝ) (hu : u ∈ Icc 3 (s-1)) :
      d*(2*a*A1 (u-3)-a^2*d*((u-3+3)*B1 (u-3))) ≤ B u/max 1 u := by
    have hu0 : 0 < u := by linarith [hu.1]
    rw [max_eq_right (by linarith [hu.1] : (1:ℝ) ≤ u)]
    apply (le_div_iff₀ hu0).2
    have h := B_joint a (u*d) (mul_pos hu0 hd) hu.1
    convert h using 1 <;> first | rfl | ring
  have hc : Continuous (fun u : ℝ => d*(2*a*A1 (u-3)-a^2*d*((u-3+3)*B1 (u-3)))) := by
    unfold A1 B1
    fun_prop
  have hg : Continuous (fun t : ℝ => (t+3)*B1 t) := by unfold B1; fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : (3:ℝ) ≤ s-1)
    (hc.intervalIntegrable 3 (s-1)) ((div_continuous B_continuous).intervalIntegrable 3 (s-1)) hh
  rw [intervalIntegral.integral_const_mul,
    weighted_integral A2_deriv B2_deriv A1_continuous hg A2_zero B2_zero] at h
  rw [show s-1-3=s-4 by ring] at h
  exact h

theorem D_joint (a d : ℝ) (hd : 0 < d) {s : ℝ} (hs : 5 ≤ s) :
    d*(2*a*A3 (s-5)-a^2*d*B3 (s-5)) ≤ D s := by
  have hh (u : ℝ) (hu : u ∈ Icc 4 (s-1)) :
      d*(2*a*A2 (u-4)-a^2*d*((u-4+4)*B2 (u-4))) ≤ C u/max 1 u := by
    have hu0 : 0 < u := by linarith [hu.1]
    rw [max_eq_right (by linarith [hu.1] : (1:ℝ) ≤ u)]
    apply (le_div_iff₀ hu0).2
    have h := C_joint a (u*d) (mul_pos hu0 hd) hu.1
    convert h using 1 <;> first | rfl | ring
  have hc : Continuous (fun u : ℝ => d*(2*a*A2 (u-4)-a^2*d*((u-4+4)*B2 (u-4)))) := by
    unfold A2 B2
    fun_prop
  have hg : Continuous (fun t : ℝ => (t+4)*B2 t) := by unfold B2; fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : (4:ℝ) ≤ s-1)
    (hc.intervalIntegrable 4 (s-1)) ((div_continuous C_continuous).intervalIntegrable 4 (s-1)) hh
  rw [intervalIntegral.integral_const_mul,
    weighted_integral A3_deriv B3_deriv A2_continuous hg A3_zero B3_zero] at h
  rw [show s-1-4=s-5 by ring] at h
  exact h

theorem E_joint (a d : ℝ) (hd : 0 < d) {s : ℝ} (hs : 6 ≤ s) :
    d*(2*a*A4 (s-6)-a^2*d*B4 (s-6)) ≤ E s := by
  have hh (u : ℝ) (hu : u ∈ Icc 5 (s-1)) :
      d*(2*a*A3 (u-5)-a^2*d*((u-5+5)*B3 (u-5))) ≤ D u/max 1 u := by
    have hu0 : 0 < u := by linarith [hu.1]
    rw [max_eq_right (by linarith [hu.1] : (1:ℝ) ≤ u)]
    apply (le_div_iff₀ hu0).2
    have h := D_joint a (u*d) (mul_pos hu0 hd) hu.1
    convert h using 1 <;> first | rfl | ring
  have hc : Continuous (fun u : ℝ => d*(2*a*A3 (u-5)-a^2*d*((u-5+5)*B3 (u-5)))) := by
    unfold A3 B3
    fun_prop
  have hg : Continuous (fun t : ℝ => (t+5)*B3 t) := by unfold B3; fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by linarith : (5:ℝ) ≤ s-1)
    (hc.intervalIntegrable 5 (s-1)) ((div_continuous D_continuous).intervalIntegrable 5 (s-1)) hh
  rw [intervalIntegral.integral_const_mul,
    weighted_integral A4_deriv B4_deriv A3_continuous hg A4_zero B4_zero] at h
  rw [show s-1-5=s-6 by ring] at h
  exact h

end EJoint
