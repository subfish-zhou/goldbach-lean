import F1JointQuadratic

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1RemainingRecovery
open scoped Interval
namespace F1JointFTC

def primitive (u : ℝ) : ℝ :=
  polePrimitive 0 partA 0 0 u+polePrimitive (-(1327/200)) partB 0 0 u+
    polePrimitive (-2) partC partD partE u+quadraticPrimitive partF partG u

theorem primitive_deriv {u : ℝ} (hu : 2 ≤ u) : HasDerivAt primitive (kernel u) u := by
  have h1 := polePrimitive_hasDerivAt 0 partA 0 0 u (by linarith)
  have h2 := polePrimitive_hasDerivAt (-(1327/200)) partB 0 0 u (by linarith)
  have h3 := polePrimitive_hasDerivAt (-2) partC partD partE u (by linarith)
  have h4 := quadraticPrimitive_deriv partF partG hu
  rw [kernel_partial hu]
  convert ((h1.add h2).add h3).add h4 using 1 <;> first | rfl | skip
  simp only [poleKernel,partialKernel,sub_zero,zero_div,add_zero,sub_neg_eq_add]
  ring

theorem kernel_continuousOn : ContinuousOn kernel (Icc 2 (927/200)) := by
  intro u hu
  have hu0 : 0 < u := by linarith [hu.1]
  have hn : Continuous (fun u : ℝ => 2*momentWeight u) := by unfold momentWeight; fun_prop
  have hd : Continuous momentDenom := by unfold momentDenom; fun_prop
  apply (hn.continuousAt.div hd.continuousAt ?_).continuousWithinAt
  unfold momentDenom
  positivity

def exactMass : ℝ := primitive (927/200)-primitive 2

/-- Exact FTC on the whole original interval; no square or moment truncation. -/
theorem kernel_integral : (∫ u in (2:ℝ)..(927/200), kernel u) = exactMass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitive_deriv
    have he : Set.uIcc (2:ℝ) (927/200)=Icc 2 (927/200) := uIcc_of_le (by norm_num)
    rw [he] at hu
    exact hu.1
  · exact kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num)

end F1JointFTC
