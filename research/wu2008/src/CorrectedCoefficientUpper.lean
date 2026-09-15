import GlobalLowerSlack

/-! A complete upper corridor for the literal corrected coefficient.
The full fixed admissible mask is retained. Its existing support rectangle
is used only as a majorant, never as a replacement definition. -/
noncomputable section
open Real Set MeasureTheory
open Wu2008DoubleSieve
namespace CorrectedCoefficientUpper
open FullAdmissibleSeed
open FullAdmissibleStrength (a b v)

/-- Uniform denominator floor on the full original admissible region. -/
def denominatorFloor : ℝ := a*b*(2*a)
def kernelCap : ℝ := (1/500)/denominatorFloor
def gammaUpper : ℝ := 4*kernelCap*(b-a)*(v-b)

theorem fixed_parameters : 0 < a ∧ 0 < b ∧ a ≤ b ∧ b ≤ v ∧
    0 < denominatorFloor ∧ 0 ≤ kernelCap := by
  norm_num [a,b,v,denominatorFloor,kernelCap,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem mask_support {z : ℝ × ℝ}
    (hz : truncatedSixthLowerAdmissibleRegion (1/1000) z.1 z.2) : z ∈ FullAdmissibleStrength.R := by
  exact ⟨⟨hz.1.1,hz.1.2.1⟩,⟨hz.1.2.2.1,hz.2⟩⟩

theorem denominator_floor {z : ℝ × ℝ}
    (hz : truncatedSixthLowerAdmissibleRegion (1/1000) z.1 z.2) :
    denominatorFloor ≤ z.1*z.2*(truncatedSixthLowerC 0-z.1-z.2) := by
  have hp := fixed_parameters
  have hx : a ≤ z.1 := hz.1.1
  have hy : b ≤ z.2 := hz.1.2.2.1
  have hc : 2*a ≤ truncatedSixthLowerC 0-z.1-z.2 := by
    have h := hz.1.2.2.2.2
    unfold truncatedSixthLowerC at *
    change z.1+z.2 ≤ 1/2-1/1000-2*a at h
    linarith only [h]
  exact mul_le_mul (mul_le_mul hx hy hp.2.1.le (hp.1.le.trans hx)) hc
    (mul_nonneg (by norm_num) hp.1.le) (mul_nonneg (hp.1.le.trans hx) (hp.2.1.le.trans hy))

theorem full_kernel_cap (z : ℝ × ℝ) : uniformKernel (1/1000) z ≤ kernelCap := by
  by_cases hz : truncatedSixthLowerAdmissibleRegion (1/1000) z.1 z.2
  · have hz0 := region_mono (by norm_num : (0:ℝ) ≤ 1/1000) hz
    have hb := truncatedSixthLower_region_bounds (δ := 0) le_rfl hz0.1
    have hs : seed (truncatedSixthLowerS 0 z.1 z.2) ≤ 1/500 := by
      unfold seed
      apply max_le (by norm_num)
      linarith only [hb.2.2.2.1]
    rw [uniformKernel,if_pos hz]
    exact div_le_div₀ (by norm_num) hs fixed_parameters.2.2.2.2.1
      (denominator_floor hz)
  · rw [uniformKernel,if_neg hz]
    exact fixed_parameters.2.2.2.2.2

theorem full_kernel_support :
    FullAdmissibleStrength.R.indicator (uniformKernel (1/1000)) = uniformKernel (1/1000) := by
  classical
  funext z
  by_cases hz : z ∈ FullAdmissibleStrength.R
  · exact Set.indicator_of_mem hz _
  · rw [Set.indicator_of_notMem hz,uniformKernel,if_neg (fun h => hz (mask_support h))]

theorem cap_integrable : IntegrableOn (fun _ : ℝ × ℝ => kernelCap) FullAdmissibleStrength.R :=
  continuous_const.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem cap_integral : (∫ _z in FullAdmissibleStrength.R, kernelCap) = kernelCap*(b-a)*(v-b) := by
  have hi := cap_integrable
  unfold FullAdmissibleStrength.R at hi ⊢
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod _ hi]
  simp_rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le fixed_parameters.2.2.1]
  simp_rw [← intervalIntegral.integral_of_le fixed_parameters.2.2.2.1]
  simp only [intervalIntegral.integral_const,smul_eq_mul]
  ring

/-- This upper bound controls the entire literal Gamma6, not an inner wedge. -/
theorem gamma_upper : Gamma6 ≤ gammaUpper := by
  have hi := uniform_integrable (by norm_num : (0:ℝ) < 1/1000) le_rfl
  have hu := setIntegral_mono_on hi.integrableOn cap_integrable
    (measurableSet_Icc.prod measurableSet_Icc) (fun z _ => full_kernel_cap z)
  have he : (∫ z : ℝ × ℝ, uniformKernel (1/1000) z) =
      ∫ z in FullAdmissibleStrength.R, uniformKernel (1/1000) z := by
    conv_lhs => rw [← full_kernel_support]
    exact integral_indicator (measurableSet_Icc.prod measurableSet_Icc)
  rw [cap_integral] at hu
  unfold Gamma6 FullAdmissibleSeed.Gamma gammaUpper
  rw [he]
  linarith only [hu]

theorem gamma_upper_exact : gammaUpper = 17619495957/515000000000 := by
  norm_num [gammaUpper,kernelCap,denominatorFloor,a,b,v,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

/-- Both endpoints enclose the complete once-only sixth correction. -/
theorem sixth_correction_interval :
    (FullAdmissibleStrength.polynomialPayment-47/481250)/4 ≤
      (Gamma6-47/481250)/4 ∧
    (Gamma6-47/481250)/4 ≤ (gammaUpper-47/481250)/4 := by
  have hl := FullAdmissibleStrength.polynomial_payment
  have hu := gamma_upper
  constructor <;> linarith only [hl,hu]

/-- These are the original small-segment endpoints, not the fifth triangle. -/
theorem original_small_endpoints : OriginalU8.SymbolicSmallGain.a = (100/1327:ℝ) ∧
    OriginalU8.SymbolicSmallGain.b = (1/10:ℝ) := by
  constructor <;> rfl

theorem small_correction_interval :
    U8ActualThreshold.gainLower ≤ 2*(U8CanonicalMother.L-U8CanonicalMother.I) ∧
    2*(U8CanonicalMother.L-U8CanonicalMother.I) ≤ U8ActualThreshold.gainUpper :=
  U8ActualThreshold.exact_weight_gain_bounds

def upperCoefficient : ℝ := FifthReciprocalAffineUpper.upperRational+
  (gammaUpper-47/481250)/4+U8ActualThreshold.gainUpper

/-- Complete upper bound for the same literal coefficient as the frozen lower. -/
theorem actual_upper : U8CanonicalMother.improvedCoefficient < upperCoefficient := by
  have ho := FifthReciprocalAffineUpper.actual_upper
  have hs := sixth_correction_interval.2
  have hg := small_correction_interval.2
  rw [U8ActualThreshold.actual_identity]
  unfold upperCoefficient
  linarith only [ho,hs,hg]

theorem actual_corridor :
    GlobalLowerSlack.lowerCoefficient < U8CanonicalMother.improvedCoefficient ∧
    U8CanonicalMother.improvedCoefficient < upperCoefficient :=
  ⟨GlobalLowerSlack.actual_lower,actual_upper⟩

/-- Certificate widths, not a ranking of the actual unpaid quantities. -/
def oldWidth : ℝ := FifthReciprocalAffineUpper.upperRational-GlobalLowerSlack.lowerOld
def sixthWidth : ℝ := (gammaUpper-FullAdmissibleStrength.polynomialPayment)/4
def smallWidth : ℝ := U8ActualThreshold.gainUpper-U8ActualThreshold.gainLower

theorem width_identity : upperCoefficient-GlobalLowerSlack.lowerCoefficient =
    oldWidth+sixthWidth+smallWidth := by
  unfold upperCoefficient GlobalLowerSlack.lowerCoefficient U8ActualThreshold.lowerCoefficient
    oldWidth GlobalLowerSlack.lowerOld sixthWidth smallWidth
  ring

theorem small_upper_exact : U8ActualThreshold.gainUpper =
    16961176844240891536893483709663/3406654627855366052891620253700000 := by
  norm_num [U8ActualThreshold.gainUpper,U8ActualThreshold.weightUpper,
    U8ActualThreshold.ratio,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b,
    JointLogTotalComparison.V,SharpLogRecurrence.upperLog,SharpLogRecurrence.lowerLog]

theorem small_upper_bounds : (4978/1000000:ℝ) < U8ActualThreshold.gainUpper ∧
    U8ActualThreshold.gainUpper < 4979/1000000 := by
  rw [small_upper_exact]
  norm_num

theorem correction_upper_bounds : (13507/1000000:ℝ) <
    (gammaUpper-47/481250)/4+U8ActualThreshold.gainUpper ∧
    (gammaUpper-47/481250)/4+U8ActualThreshold.gainUpper < 13508/1000000 := by
  rw [gamma_upper_exact,small_upper_exact]
  norm_num

theorem upper_coefficient_bounds : (911610/1000000:ℝ) < upperCoefficient ∧
    upperCoefficient < 911612/1000000 := by
  have ho := FifthReciprocalAffineUpper.upper_bounds
  have hc := correction_upper_bounds
  unfold upperCoefficient
  constructor <;> linarith only [ho.1,ho.2,hc.1,hc.2]

theorem rational_actual_corridor :
    (831353/1000000:ℝ) < U8CanonicalMother.improvedCoefficient ∧
    U8CanonicalMother.improvedCoefficient < 911612/1000000 :=
  ⟨GlobalLowerSlack.lowerCoefficient_bounds.1.trans actual_corridor.1,
    actual_corridor.2.trans upper_coefficient_bounds.2⟩

theorem old_width_bounds : (71585/1000000:ℝ) < oldWidth ∧ oldWidth < 71587/1000000 := by
  have hu := FifthReciprocalAffineUpper.upper_bounds
  have hl := GlobalLowerSlack.lowerOld_bounds
  unfold oldWidth
  constructor <;> linarith only [hu.1,hu.2,hl.1,hl.2]

theorem sixth_width_bounds : (8294/1000000:ℝ) < sixthWidth ∧ sixthWidth < 8295/1000000 := by
  unfold sixthWidth
  rw [gamma_upper_exact,FullAdmissibleStrength.polynomial_payment_exact]
  norm_num

theorem small_width_bounds : (377/1000000:ℝ) < smallWidth ∧ smallWidth < 378/1000000 := by
  unfold smallWidth
  rw [small_upper_exact,U8ActualThreshold.gainLower_exact]
  norm_num

/-- All three widths are proved from actual enclosing pairs. -/
theorem component_corridors :
    GlobalLowerSlack.lowerOld < JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < FifthReciprocalAffineUpper.upperRational ∧
    FullAdmissibleStrength.polynomialPayment ≤ Gamma6 ∧ Gamma6 ≤ gammaUpper ∧
    U8ActualThreshold.gainLower ≤ 2*(U8CanonicalMother.L-U8CanonicalMother.I) ∧
    2*(U8CanonicalMother.L-U8CanonicalMother.I) ≤ U8ActualThreshold.gainUpper :=
  ⟨GlobalLowerSlack.old_actual_lower,FifthReciprocalAffineUpper.actual_upper,
    FullAdmissibleStrength.polynomial_payment,gamma_upper,
    small_correction_interval.1,small_correction_interval.2⟩

/-- Only certificate widths are ranked; no actual slack ranking is inferred. -/
theorem certificate_width_dominance :
    0 < smallWidth ∧ smallWidth < sixthWidth ∧ 8*(sixthWidth+smallWidth) < oldWidth := by
  have ho := old_width_bounds
  have hs := sixth_width_bounds
  have hg := small_width_bounds
  constructor
  · linarith only [hg.1]
  constructor <;> linarith only [ho.1,hs.1,hs.2,hg.2]

/-- More than eight ninths of this corridor's width comes from the old package. -/
theorem old_package_fraction_of_width :
    8*(upperCoefficient-GlobalLowerSlack.lowerCoefficient) < 9*oldWidth := by
  rw [width_identity]
  linarith only [certificate_width_dominance.2.2]

/-- Retaining the old upper endpoint cannot prove the corrected object below target,
even if both added components could be tightened down to their certified lower ends.
This statement concerns an upper-certificate architecture, not the actual sign. -/
theorem old_upper_plus_lower_corrections_above_target :
    8*log (5000/4469) < FifthReciprocalAffineUpper.upperRational+
      (FullAdmissibleStrength.polynomialPayment-47/481250)/4+U8ActualThreshold.gainLower := by
  have ht := JointLogTotalComparison.log_le_V (show (1:ℝ) ≤ 5000/4469 by norm_num)
  have ho := FifthReciprocalAffineUpper.upper_bounds.1
  have hr : 8*JointLogTotalComparison.V (5000/4469) < (898103/1000000:ℝ)+
      (FullAdmissibleStrength.polynomialPayment-47/481250)/4+U8ActualThreshold.gainLower := by
    rw [FullAdmissibleStrength.polynomial_payment_exact,U8ActualThreshold.gainLower_exact]
    norm_num [JointLogTotalComparison.V,SharpLogRecurrence.upperLog,SharpLogRecurrence.lowerLog]
  linarith only [ht,ho,hr]

theorem old_upper_architecture_obstruction (s g : ℝ)
    (hs : FullAdmissibleStrength.polynomialPayment ≤ s)
    (hg : U8ActualThreshold.gainLower ≤ g) :
    8*log (5000/4469) < FifthReciprocalAffineUpper.upperRational+(s-47/481250)/4+g := by
  linarith only [old_upper_plus_lower_corrections_above_target,hs,hg]

/-- Both the actual value and the target lie inside this certified corridor.
No ordering between those two interior points is asserted. -/
theorem target_inside_corridor :
    GlobalLowerSlack.lowerCoefficient < 8*log (5000/4469) ∧
    8*log (5000/4469) < upperCoefficient := by
  refine ⟨GlobalLowerSlack.certificate_below_target,?_⟩
  have hs := FullAdmissibleStrength.polynomial_payment.trans gamma_upper
  have hg := small_correction_interval.1.trans small_correction_interval.2
  exact old_upper_architecture_obstruction gammaUpper U8ActualThreshold.gainUpper hs hg

/-- The still-unclosed strict comparison, expressed with the literal upper deficit. -/
theorem actual_target_iff_upper_deficit :
    8*log (5000/4469) < U8CanonicalMother.improvedCoefficient ↔
    upperCoefficient-U8CanonicalMother.improvedCoefficient <
      upperCoefficient-8*log (5000/4469) := by
  constructor <;> intro h <;> linarith only [h]

end CorrectedCoefficientUpper
