import MiddleInitialActual

/-! A full-mask upper bound using the original seed boundary.
The positive-part inequality is universal algebra, not a Taylor expansion.
The original rectangle is used as a nonnegative majorant domain only. -/
noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FullAdmissibleSeed
open FullAdmissibleStrength (a b v L U R quadratic_integral)
namespace GammaFullUpper

def m : ℝ := a+b
def c : ℝ := L-m
def denominator : ℝ := a*(U-a)*(1/2-U)
def K : ℝ := 1/(4*c*750*a*denominator)
def majorant (x y : ℝ) : ℝ := K*(x+y-m)^2

theorem parameters : 0 < a ∧ a ≤ b ∧ b ≤ v ∧ 0 < c ∧
    0 < denominator ∧ 0 < K ∧ 0 ≤ L+U-a-1/2 := by
  norm_num [a,b,v,L,U,m,c,denominator,K,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

/-- On the positive seed support, the sum and product constraints cooperate. -/
theorem active_denominator {x y : ℝ}
    (hr : truncatedSixthLowerAdmissibleRegion (1/1000) x y)
    (hs : L ≤ x+y) : denominator ≤ x*y*(1/2-x-y) := by
  have hp := parameters
  have hx : a ≤ x := hr.1.1
  have hy : b ≤ y := hr.1.2.2.1
  have hu : x+y ≤ U := hr.1.2.2.2.2
  have hya : a ≤ y := hp.2.1.trans hy
  have hprod : a*(x+y-a) ≤ x*y := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hya)]
  have hz : 0 ≤ 1/2-x-y := by
    have he : U < (1/2:ℝ) := by
      norm_num [U,a,truncatedSixthLowerAlpha]
    linarith only [hu,he]
  have hsum : 0 ≤ x+y+U-a-1/2 := by
    linarith only [hs,hp.2.2.2.2.2.2]
  have hpair : (U-a)*(1/2-U) ≤ (x+y-a)*(1/2-x-y) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hu) hsum]
  have h1 := mul_le_mul_of_nonneg_left hpair hp.1.le
  have h2 := mul_le_mul_of_nonneg_right hprod hz
  unfold denominator
  nlinarith only [h1,h2]

/-- The complete original seed, rewritten without changing its positive part. -/
theorem seed_identity (x y : ℝ) :
    seed (truncatedSixthLowerS 0 x y) = max 0 ((x+y-L)/(750*a)) := by
  unfold seed truncatedSixthLowerS truncatedSixthLowerC
  congr 1
  unfold L a
  field_simp [ne_of_gt truncatedSixthLower_parameters.1]
  ring

/-- A global square inequality, with its scale fixed by the original endpoints. -/
theorem positive_part_upper (s : ℝ) :
    max 0 ((s-L)/(750*a)) ≤ (s-m)^2/(4*c*750*a) := by
  have hp := parameters
  have ha : 0 < a := hp.1
  have hc : 0 < c := hp.2.2.2.1
  have hd : 0 < 4*c*750*a := by positivity
  apply max_le
  · positivity
  · apply (le_div_iff₀ hd).2
    have he : (s-L)/(750*a)*(4*c*750*a) = 4*c*(s-L) := by
      field_simp [ne_of_gt hp.1]
    rw [he]
    unfold c
    nlinarith only [sq_nonneg (s-m-2*(L-m))]

/-- This pointwise comparison retains every branch of the literal full mask. -/
theorem full_kernel_upper (z : ℝ × ℝ) :
    uniformKernel (1/1000) z ≤ majorant z.1 z.2 := by
  have hp := parameters
  have ha : 0 < a := hp.1
  have hk : 0 < K := hp.2.2.2.2.2.1
  have hnon : 0 ≤ majorant z.1 z.2 := by unfold majorant; positivity
  by_cases hr : truncatedSixthLowerAdmissibleRegion (1/1000) z.1 z.2
  · rw [uniformKernel,if_pos hr,seed_identity]
    by_cases hs : L ≤ z.1+z.2
    · have hd := denominator_pos (δ := 0) le_rfl
        (region_mono (by norm_num : (0:ℝ) ≤ 1/1000) hr)
      have hden := active_denominator hr hs
      have hn : 0 ≤ max 0 ((z.1+z.2-L)/(750*a)) := le_max_left _ _
      have h1 := div_le_div_of_nonneg_left hn hp.2.2.2.2.1
        (show denominator ≤ z.1*z.2*(truncatedSixthLowerC 0-z.1-z.2) by
          simpa [truncatedSixthLowerC] using hden)
      have h2 := div_le_div_of_nonneg_right (positive_part_upper (z.1+z.2))
        hp.2.2.2.2.1.le
      have he : ((z.1+z.2-m)^2/(4*c*750*a))/denominator = majorant z.1 z.2 := by
        unfold majorant K
        ring
      exact h1.trans (he ▸ h2)
    · have hn : (z.1+z.2-L)/(750*a) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) (by positivity)
      rw [max_eq_left hn,zero_div]
      exact hnon
  · rw [uniformKernel,if_neg hr]
    exact hnon

def p0 : ℝ := v-b
def p1 : ℝ := v^2-b^2-2*m*(v-b)
def p2 : ℝ := (v^3-b^3)/3-m*(v^2-b^2)+m^2*(v-b)
def moment : ℝ := (p0*b^3/3+p1*b^2/2+p2*b)-(p0*a^3/3+p1*a^2/2+p2*a)
def gammaUpper : ℝ := 4*K*moment

theorem inner_integral (x : ℝ) :
    (∫ y in b..v, majorant x y) = K*(p0*x^2+p1*x+p2) := by
  have he : (fun y : ℝ => majorant x y) =
      (fun y => K*(1*y^2+(2*x-2*m)*y+(x-m)^2)) := by
    funext y; unfold majorant; ring
  rw [he,intervalIntegral.integral_const_mul,quadratic_integral]
  unfold p0 p1 p2
  ring

theorem iterated_integral :
    (∫ x in a..b, ∫ y in b..v, majorant x y) = K*moment := by
  simp_rw [inner_integral]
  rw [intervalIntegral.integral_const_mul,quadratic_integral]
  rfl

theorem majorant_integrable : IntegrableOn (fun z : ℝ × ℝ => majorant z.1 z.2) FullAdmissibleStrength.R := by
  exact (by unfold majorant; fun_prop : Continuous (fun z : ℝ × ℝ => majorant z.1 z.2)).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

theorem rectangle_integral : (∫ z in FullAdmissibleStrength.R, majorant z.1 z.2) = K*moment := by
  have hi := majorant_integrable
  unfold FullAdmissibleStrength.R at hi ⊢
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod _ hi]
  simp_rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le parameters.2.1]
  simp_rw [← intervalIntegral.integral_of_le parameters.2.2.1]
  exact iterated_integral

/-- An actual bound on the full original integral, not an inner-region integral. -/
theorem gamma_upper : Gamma6 ≤ gammaUpper := by
  have hi := uniform_integrable (by norm_num : (0:ℝ) < 1/1000) le_rfl
  have hu := setIntegral_mono_on hi.integrableOn majorant_integrable
    (measurableSet_Icc.prod measurableSet_Icc) (fun z _ => full_kernel_upper z)
  have he : (∫ z : ℝ × ℝ, uniformKernel (1/1000) z) =
      ∫ z in FullAdmissibleStrength.R, uniformKernel (1/1000) z := by
    conv_lhs => rw [← CorrectedCoefficientUpper.full_kernel_support]
    exact integral_indicator (measurableSet_Icc.prod measurableSet_Icc)
  rw [rectangle_integral] at hu
  unfold Gamma6 FullAdmissibleSeed.Gamma gammaUpper
  rw [he]
  linarith only [hu]

theorem gamma_upper_exact : gammaUpper =
    759283541262335374255825033/98398091921967866548800000000 := by
  norm_num [gammaUpper,K,moment,p0,p1,p2,c,m,denominator,L,U,v,a,b,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

/-- More than three quarters of the previous full Gamma upper are removed. -/
theorem substantial_descent : 4*gammaUpper < CorrectedCoefficientUpper.gammaUpper := by
  rw [gamma_upper_exact,CorrectedCoefficientUpper.gamma_upper_exact]
  norm_num

end GammaFullUpper
