import F1KernelPolynomialPayment

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment
open scoped Interval
namespace F1RemainingRecovery

/-- Unconditional quantitative recovery from the actual original C integral. -/
theorem kernelPayment_le_actual_gap {s : ℝ} (hs : 4 ≤ s) :
    kernelPayment s ≤ Wu08OriginalFirstSteps.C s-cLowerMass s := by
  have ho : (2:ℝ) ≤ s-2 := by linarith
  have h1 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) ho (cExactKernel_continuousOn s)
  have h2 := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) ho (cLowerKernel_continuousOn s)
  have hc : Continuous (fun u : ℝ => (u-2)^5*(s-2-u)/kernelDenom s) := by fun_prop
  have hm := intervalIntegral.integral_mono_on ho (hc.intervalIntegrable 2 (s-2))
    (h1.sub h2) (fun _ hu => polynomial_kernel_payment hu)
  rw [polynomial_kernel_integral,intervalIntegral.integral_sub h1 h2] at hm
  rw [C_flat hs]
  exact hm

/-- Literal original endpoint: no condition on a replacement lower kernel. -/
theorem kernelPayment_le_kernelRecovery :
    kernelPayment (1327/200) ≤ FirstActualRecovery.kernelRecovery := by
  unfold FirstActualRecovery.kernelRecovery
  rw [← cLowerMass_eq_endpointMass]
  exact kernelPayment_le_actual_gap (by norm_num)

theorem kernelPayment_pos {s : ℝ} (hs : 4 < s) : 0 < kernelPayment s := by
  unfold kernelPayment
  exact div_pos (pow_pos (sub_pos.mpr hs) _) (mul_pos (by norm_num) (kernelDenom_pos hs.le))

end F1RemainingRecovery
