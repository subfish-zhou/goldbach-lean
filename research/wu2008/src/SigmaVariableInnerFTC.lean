import D0FullFTC
import CorrectionSigmaActualRemainder

noncomputable section
namespace SigmaVariableFull
open Real Set MeasureTheory
open scoped Interval

/-- The original sigma change of variable; no endpoint coefficient is frozen. -/
def argument (t v : ℝ) : ℝ := (t+1)/(v-1)
def density (t v : ℝ) : ℝ := RemainingHf.basicLower (argument t v)/v
def innerPrimitive (t v : ℝ) : ℝ :=
  -D0FullDensity.zeroPrimitive (argument t v)+
    TerminalE.primitive (-(t+1)) (argument t v)

theorem pole_quadratic {t : ℝ} (ht : t ∈ Icc 1 3) :
    TerminalE.q (-(t+1)) < 0 := by
  unfold TerminalE.q
  have hm : 0 ≤ t*(3-t) := mul_nonneg (by linarith [ht.1]) (by linarith [ht.2])
  nlinarith [ht.1]

theorem argument_bounds {t v : ℝ} (ht : 1 ≤ t) (hv : v ∈ Icc 3 (t+2)) :
    1 ≤ argument t v ∧ argument t v ≤ (t+1)/2 :=
  CorrectionSigmaVariable.argument_bounds ht hv

theorem argument_deriv {t v : ℝ} (hv : 3 ≤ v) :
    HasDerivAt (argument t) (-(t+1)/(v-1)^2) v := by
  have hv1 : v-1 ≠ 0 := by linarith
  convert (((hasDerivAt_id v).sub_const 1).inv hv1).const_mul (t+1) using 1 <;>
    first | rfl | (dsimp; ring)

/-- Both coalescent zero and forced negative poles, with their complete Jacobian. -/
theorem innerPrimitive_deriv {t v : ℝ} (ht : t ∈ Icc 1 3)
    (hv : v ∈ Icc 3 (t+2)) :
    HasDerivAt (innerPrimitive t) (density t v) v := by
  have hx := (argument_bounds ht.1 hv).1
  have hp : -(t+1) ≠ 0 := by linarith [ht.1]
  have hp1 : -(t+1)+1 ≠ 0 := by linarith [ht.1]
  have hxp : argument t v-(-(t+1)) ≠ 0 := by linarith [ht.1]
  have hv0 : v ≠ 0 := by linarith [hv.1]
  have hv1 : v-1 ≠ 0 := by linarith [hv.1]
  have ht1 : t+1 ≠ 0 := by linarith [ht.1]
  have h0 := (D0FullDensity.zeroPrimitive_deriv hx).comp v (argument_deriv hv.1)
  have hpole := (D0FullDensity.primitive_deriv hp hp1 (pole_quadratic ht).ne hx hxp).comp v
    (argument_deriv hv.1)
  convert h0.neg.add hpole using 1 <;> first | rfl | skip
  have he : argument t v-(-(t+1))=(t+1)*v/(v-1) := by
    unfold argument
    field_simp
    ring
  rw [he]
  unfold density argument
  field_simp [hv0,hv1,ht1]
  ring

theorem density_integrable {t : ℝ} (ht : 1 ≤ t) :
    IntervalIntegrable (density t) volume 3 (t+2) := by
  have he : density t=fun v => CorrectionSigmaVariable.oldDensity t v+
      CorrectionSigmaVariable.variation t v/v := by
    funext v
    exact CorrectionSigmaVariable.density_balance t v
  rw [he]
  exact (CorrectionSigmaVariable.oldDensity_integrable ht).add
    (CorrectionSigmaVariable.variation_integrable ht)

/-- Exact complete inner integral on the entire original outer domain. -/
def innerMass (t : ℝ) : ℝ := innerPrimitive t (t+2)-innerPrimitive t 3

theorem density_integral {t : ℝ} (ht : t ∈ Icc 1 3) :
    (∫ v in (3:ℝ)..t+2,density t v)=innerMass t := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro v hv
    rw [uIcc_of_le (by linarith [ht.1] : (3:ℝ) ≤ t+2)] at hv
    exact innerPrimitive_deriv ht hv
  · exact density_integrable ht.1

theorem innerMass_balance {t : ℝ} (ht : t ∈ Icc 1 3) :
    innerMass t=SigmaInnerEndpointRecovery.kernel t+CorrectionSigmaVariable.variationMass t := by
  rw [← density_integral ht,← CorrectionSigmaVariable.oldDensity_integral ht.1]
  unfold CorrectionSigmaVariable.variationMass
  rw [← intervalIntegral.integral_add (CorrectionSigmaVariable.oldDensity_integrable ht.1)
    (CorrectionSigmaVariable.variation_integrable ht.1)]
  apply intervalIntegral.integral_congr
  intro v _
  exact CorrectionSigmaVariable.density_balance t v

theorem innerMass_le_sigma {t : ℝ} (ht : t ∈ Icc 1 3) :
    innerMass t ≤ NodeExtension.sigma 3 (t+2) (t+1) := by
  rw [innerMass_balance ht]
  exact CorrectionSigmaVariable.kernel_add_variation_le_sigma ht.1

theorem innerMass_endpoints {t : ℝ} (ht : t ∈ Icc 1 3) :
    innerMass t= -D0FullDensity.zeroPrimitive 1+TerminalE.primitive (-(t+1)) 1+
      D0FullDensity.zeroPrimitive ((t+1)/2)-TerminalE.primitive (-(t+1)) ((t+1)/2) := by
  have ht1 : t+1 ≠ 0 := by linarith [ht.1]
  have he : argument t (t+2)=1 := by
    unfold argument
    rw [show t+2-1=t+1 by ring,div_self ht1]
  unfold innerMass innerPrimitive
  rw [he]
  unfold argument
  norm_num
  ring

end SigmaVariableFull
