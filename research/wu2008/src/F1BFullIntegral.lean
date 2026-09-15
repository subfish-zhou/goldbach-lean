import F1BFullQuadratic

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1SecondLogRecovery
open scoped Interval
namespace F1BFullFTC

def primitiveOne (u : ℝ) : ℝ :=
  polePrimitive (-2) oneA 0 0 u+polePrimitive (2/3) oneB 0 0 u+
    polePrimitive (-(1727/600)) oneC oneD oneE u+quadPrimitiveOne oneF oneG u

theorem primitiveOne_deriv {u : ℝ} (hu : 2 ≤ u) :
    HasDerivAt primitiveOne (kernelOne u) u := by
  have h1 := polePrimitive_hasDerivAt (-2) oneA 0 0 u (by linarith)
  have h2 := polePrimitive_hasDerivAt (2/3) oneB 0 0 u (by linarith)
  have h3 := polePrimitive_hasDerivAt (-(1727/600)) oneC oneD oneE u (by linarith)
  have h4 := quadPrimitiveOne_deriv oneF oneG hu
  rw [partial_one hu]
  convert ((h1.add h2).add h3).add h4 using 1 <;> first | rfl | skip
  simp only [poleKernel,partialOne,zero_div,add_zero,sub_neg_eq_add]
  ring

theorem kernelOne_continuousOn : ContinuousOn kernelOne (Icc 2 (927/200)) := by
  intro u hu
  have hn : Continuous (fun u : ℝ => 8*weight u) := by unfold weight; fun_prop
  have hd : Continuous denomOne := by unfold denomOne errorDenomOne; fun_prop
  exact (hn.continuousAt.div hd.continuousAt (denominators_pos hu.1).2.2.1.ne').continuousWithinAt

def massOne : ℝ := primitiveOne (927/200)-primitiveOne 2

theorem integral_one : (∫ u in (2:ℝ)..(927/200), kernelOne u) = massOne := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitiveOne_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 927/200)] at hu
    exact hu.1
  · exact kernelOne_continuousOn.intervalIntegrable_of_Icc (by norm_num)

def primitiveTwo (u : ℝ) : ℝ :=
  polePrimitive (-2) twoA 0 0 u+polePrimitive (2/3) twoB 0 0 u+
    polePrimitive (-(3581/200)) twoC twoD twoE u+quadPrimitiveTwo twoF twoG u

theorem primitiveTwo_deriv {u : ℝ} (hu : 2 ≤ u) :
    HasDerivAt primitiveTwo (kernelTwo u) u := by
  have h1 := polePrimitive_hasDerivAt (-2) twoA 0 0 u (by linarith)
  have h2 := polePrimitive_hasDerivAt (2/3) twoB 0 0 u (by linarith)
  have h3 := polePrimitive_hasDerivAt (-(3581/200)) twoC twoD twoE u (by linarith)
  have h4 := quadPrimitiveTwo_deriv twoF twoG hu
  rw [partial_two hu]
  convert ((h1.add h2).add h3).add h4 using 1 <;> first | rfl | skip
  simp only [poleKernel,partialTwo,zero_div,add_zero,sub_neg_eq_add]
  ring

theorem kernelTwo_continuousOn : ContinuousOn kernelTwo (Icc 2 (927/200)) := by
  intro u hu
  have hn : Continuous (fun u : ℝ => 8*weight u) := by unfold weight; fun_prop
  have hd : Continuous denomTwo := by unfold denomTwo errorDenomTwo; fun_prop
  exact (hn.continuousAt.div hd.continuousAt (denominators_pos hu.1).2.2.2.ne').continuousWithinAt

def massTwo : ℝ := primitiveTwo (927/200)-primitiveTwo 2

theorem integral_two : (∫ u in (2:ℝ)..(927/200), kernelTwo u) = massTwo := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    apply primitiveTwo_deriv
    rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 927/200)] at hu
    exact hu.1
  · exact kernelTwo_continuousOn.intervalIntegrable_of_Icc (by norm_num)

def exactMass : ℝ := massOne+massTwo

end F1BFullFTC
