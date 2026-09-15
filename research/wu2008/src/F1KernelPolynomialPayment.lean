import F1KernelGapBase

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery
open scoped Interval
namespace F1RemainingRecovery

/-- Denominator bound forced by the original interval endpoints. -/
def kernelDenom (s : ℝ) : ℝ :=
  (s-2)*(s-1)*s^3*((s-2)^2+16*(s-2)+4)

theorem kernelDenom_pos {s : ℝ} (hs : 4 ≤ s) : 0 < kernelDenom s := by
  unfold kernelDenom
  have h2 : 0 < s-2 := by linarith
  have h1 : 0 < s-1 := by linarith
  have h0 : 0 < s := by linarith
  positivity

/-- A polynomial payment across the entire original projection, without a new cut. -/
theorem polynomial_kernel_payment {s u : ℝ} (hu : u ∈ Icc 2 (s-2)) :
    (u-2)^5*(s-2-u)/kernelDenom s ≤ cExactKernel s u-cLowerKernel s u := by
  have hs : 4 ≤ s := by linarith [hu.1,hu.2]
  have hu0 : 0 < u := by linarith [hu.1]
  have hs0 : 0 < s := by linarith
  have hs2 : 0 < s-2 := by linarith
  have hs1 : 0 < s-1 := by linarith
  have huw : 0 ≤ u-2 := by linarith [hu.1]
  have hus : 0 ≤ s-2-u := by linarith [hu.2]
  have hd : 0 < u*(s+u)*(u+2)^3*(u^2+16*u+4) := by positivity
  have hq : u^2+16*u+4 ≤ (s-2)^2+16*(s-2)+4 := by
    gcongr <;> linarith [hu.2]
  have hb : u*(s+u)*(u+2)^3*(u^2+16*u+4) ≤ 2*kernelDenom s := by
    calc
      _ ≤ (s-2)*(2*(s-1))*s^3*((s-2)^2+16*(s-2)+4) := by
        gcongr <;> first | positivity | linarith [hu.1,hu.2]
      _ = _ := by unfold kernelDenom; ring
  apply le_trans ?_ (exact_kernel_payment hu)
  calc
    (u-2)^5*(s-2-u)/kernelDenom s = 2*((u-2)^5*(s-2-u))/(2*kernelDenom s) := by ring
    _ ≤ 2*((u-2)^5*(s-2-u))/(u*(s+u)*(u+2)^3*(u^2+16*u+4)) :=
      div_le_div_of_nonneg_left (by positivity) hd hb
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring

/-- A primitive determined by the existing fifth-order error and linear triangular weight. -/
def kernelPrimitive (s u : ℝ) : ℝ :=
  ((s-4)*(u-2)^6/6-(u-2)^7/7)/kernelDenom s

theorem kernelPrimitive_deriv (s u : ℝ) :
    HasDerivAt (kernelPrimitive s) ((u-2)^5*(s-2-u)/kernelDenom s) u := by
  have hd := (hasDerivAt_id u).sub_const 2
  have h := ((((hd.pow 6).const_mul (s-4)).div_const 6).sub
    ((hd.pow 7).div_const 7)).div_const (kernelDenom s)
  convert h using 1 <;> first | rfl | (dsimp; ring)

/-- Explicit original-kernel recovery, not a changed first coefficient. -/
def kernelPayment (s : ℝ) : ℝ := (s-4)^7/(42*kernelDenom s)

theorem polynomial_kernel_integral (s : ℝ) :
    (∫ u in (2:ℝ)..(s-2), (u-2)^5*(s-2-u)/kernelDenom s) = kernelPayment s := by
  have hc : Continuous (fun u : ℝ => (u-2)^5*(s-2-u)/kernelDenom s) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => kernelPrimitive_deriv s u) (hc.intervalIntegrable 2 (s-2))]
  unfold kernelPrimitive kernelPayment
  ring

end F1RemainingRecovery
