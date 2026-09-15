import EJointOrdered
noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve SharpLogRecurrence Wu08OriginalFirstSteps
open scoped Interval
namespace EJoint

theorem A1_integral (s : ℝ) : (∫ u in 2..s-1, A0 (u-2)) = A1 (s-3) := by
  rw [shifted_integral A1_deriv A0_continuous A1_zero]
  congr 1
  ring

theorem A2_integral (s : ℝ) : (∫ u in 3..s-1, A1 (u-3)) = A2 (s-4) := by
  rw [shifted_integral A2_deriv A1_continuous A2_zero]
  congr 1
  ring

theorem A3_integral (s : ℝ) : (∫ u in 4..s-1, A2 (u-4)) = A3 (s-5) := by
  rw [shifted_integral A3_deriv A2_continuous A3_zero]
  congr 1
  ring

theorem A4_integral (s : ℝ) : (∫ u in 5..s-1, A3 (u-5)) = A4 (s-6) := by
  rw [shifted_integral A4_deriv A3_continuous A4_zero]
  congr 1
  ring

theorem B1_integral (s : ℝ) : (∫ u in 2..s-1, B0 (u-2)) = B1 (s-3) := by
  rw [shifted_integral B1_deriv B0_continuous B1_zero]
  congr 1
  ring

theorem B2_integral (s : ℝ) : (∫ u in 3..s-1, u*B1 (u-3)) = B2 (s-4) := by
  have hc : Continuous (fun t : ℝ => (t+3)*B1 t) := by unfold B1; fun_prop
  have h := shifted_integral B2_deriv hc B2_zero 3 (s-1)
  simpa only [sub_add_cancel, show s-1-3=s-4 by ring] using h

theorem B3_integral (s : ℝ) : (∫ u in 4..s-1, u*B2 (u-4)) = B3 (s-5) := by
  have hc : Continuous (fun t : ℝ => (t+4)*B2 t) := by unfold B2; fun_prop
  have h := shifted_integral B3_deriv hc B3_zero 4 (s-1)
  simpa only [sub_add_cancel, show s-1-4=s-5 by ring] using h

theorem B4_integral (s : ℝ) : (∫ u in 5..s-1, u*B3 (u-5)) = B4 (s-6) := by
  have hc : Continuous (fun t : ℝ => (t+5)*B3 t) := by unfold B3; fun_prop
  have h := shifted_integral B4_deriv hc B4_zero 5 (s-1)
  simpa only [sub_add_cancel, show s-1-5=s-6 by ring] using h

def W (s : ℝ) : ℝ := ∫ z in 5..s-1, ∫ w in 4..z-1, ∫ v in 3..w-1,
  ∫ u in 2..v-1, A0 (u-2)

def Q (s : ℝ) : ℝ := ∫ z in 5..s-1, ∫ w in 4..z-1, ∫ v in 3..w-1,
  ∫ u in 2..v-1, A0 (u-2)*(3*u^4*v*w*z)

theorem W_exact (s : ℝ) : W s = A4 (s-6) := by
  unfold W
  simp_rw [A1_integral,A2_integral,A3_integral,A4_integral]

theorem joint_weight_literal (u v w z : ℝ) :
    A0 (u-2)*(3*u^4*v*w*z) = z*(w*(v*B0 (u-2))) := by
  rw [denominator_kernel]
  ring

theorem Q_exact (s : ℝ) : Q s = B4 (s-6) := by
  unfold Q
  simp_rw [joint_weight_literal,intervalIntegral.integral_const_mul,B1_integral,
    B2_integral,B3_integral,B4_integral]

theorem full_joint_payment {s : ℝ} (hs : 6 ≤ s) : (W s)^2/Q s ≤ E s := by
  have h := E_joint (W s/Q s) 1 (by norm_num) hs
  rw [W_exact,Q_exact] at *
  by_cases hq : B4 (s-6) = 0
  · simpa [hq] using h
  · convert h using 1
    field_simp
    ring

def fixedA : ℝ := W (1327/200)/Q (1327/200)
def payment : ℝ := W (1327/200)^2/Q (1327/200)

theorem payment_le : payment ≤ E (1327/200) := full_joint_payment (by norm_num)

theorem payment_pos : 0 < payment := by
  unfold payment
  rw [W_exact,Q_exact]
  norm_num [A4,B4]

theorem payment_stronger : F1OriginalEPayment.payment < payment := by
  unfold payment F1OriginalEPayment.payment
  rw [W_exact,Q_exact]
  norm_num [A4,B4]

end EJoint
