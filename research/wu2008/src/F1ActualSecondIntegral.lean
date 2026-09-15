import F1ActualSecondPartial

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1RemainingRecovery
open scoped Interval
namespace F1ActualSecondFTC

/-- Reuse the already checked radical primitive through its forced affine argument. -/
def affinePrimitive (f g u : ℝ) : ℝ :=
  F1JointFTC.quadraticPrimitive (f/21) (g+20*f/21) (21*u-20)

theorem affinePrimitive_deriv (f g : ℝ) {u : ℝ} (hu : 2 ≤ u) :
    HasDerivAt (affinePrimitive f g) ((f*u+g)/(21*u^2-24*u+4)) u := by
  have h := (F1JointFTC.quadraticPrimitive_deriv (f/21) (g+20*f/21)
    (show 2 ≤ 21*u-20 by linarith)).comp u
    (((hasDerivAt_id u).const_mul 21).sub_const 20)
  have hq : (21*u-20)^2+16*(21*u-20)+4=21*(21*u^2-24*u+4) := by ring
  convert h using 1 <;> first | rfl | skip
  rw [hq]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def primitive (u : ℝ) : ℝ :=
  polePrimitive 0 coeffA 0 0 u+polePrimitive (-(1327/200)) coeffB 0 0 u+
    polePrimitive (2/3) coeffC coeffD coeffE u+affinePrimitive coeffF coeffG u

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h1 := polePrimitive_hasDerivAt 0 coeffA 0 0 u (by linarith)
  have h2 := polePrimitive_hasDerivAt (-(1327/200)) coeffB 0 0 u (by linarith)
  have h3 := polePrimitive_hasDerivAt (2/3) coeffC coeffD coeffE u (by linarith)
  have h4 := affinePrimitive_deriv coeffF coeffG hu
  rw [kernel_partial hu]
  convert ((h1.add h2).add h3).add h4 using 1 <;> first | rfl | skip
  simp only [poleKernel,partialKernel,sub_zero,zero_div,add_zero,sub_neg_eq_add]
  ring

theorem kernel_continuousOn : ContinuousOn kernel (Icc 2 (927/200)) := by
  intro u hu
  have hn : Continuous (fun u : ℝ => 2*momentWeight u) := by unfold momentWeight; fun_prop
  have hd : Continuous (fun u : ℝ => u*(u+1327/200)*(3*u-2)^3*(21*u^2-24*u+4)) := by
    fun_prop
  exact (hn.continuousAt.div hd.continuousAt (denominator_pos hu.1).ne').continuousWithinAt

def exactMass : ℝ := primitive (927/200)-primitive 2

/-- The entire original domain, not a new partition or a moment certificate. -/
theorem kernel_integral : (∫ u in (2:ℝ)..(927/200), kernel u) = exactMass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 927/200)] at hu
    exact hu.1
  · exact kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)

end F1ActualSecondFTC
