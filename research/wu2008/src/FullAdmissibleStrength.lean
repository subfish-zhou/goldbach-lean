import FullAdmissibleSeed

namespace Wu2008DoubleSieve.FullAdmissibleStrength
open Real Set MeasureTheory FullAdmissibleSeed
open scoped Classical
noncomputable section

def a : ℝ := truncatedSixthLowerAlpha
def b : ℝ := truncatedSixthLowerBeta
def v : ℝ := (1/2-1/1000)/2
def L : ℝ := 1/2-(7/2)*a
def U : ℝ := 1/2-1/1000-2*a
def D : ℝ := b*(1/2-a)^2/4
def A : ℝ := 1/(750*a*(U-L)*D)
def R : Set (ℝ × ℝ) := Icc a b ×ˢ Icc b v

/-- A polynomial certificate over the complete original bounding rectangle.
It is nonpositive outside the original diagonal mask or below the seed support.
This auxiliary certificate does not redefine the exact Gamma6 kernel. -/
def poly (x y : ℝ) : ℝ := A*(x+y-L)*(U-x-y)

macro "params" : tactic => `(tactic|
  norm_num [a,b,v,L,U,D,A,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])

theorem parameters : 0 < a ∧ a ≤ b ∧ b ≤ v ∧ L < U ∧ 0 < D ∧ 0 < A := by params

theorem denom_cap {x y : ℝ} (hx : x ∈ Icc a b)
    (hz : 0 ≤ 1/2-x-y) (hy : 0 ≤ y) :
    x*y*(1/2-x-y) ≤ D := by
  have hp := parameters
  have hx0 : 0 ≤ x := hp.1.le.trans hx.1
  have hxhi : x ≤ 1/2 := by have h := hx.2; norm_num [b,truncatedSixthLowerBeta] at h; linarith
  have hquad : y*(1/2-x-y) ≤ (1/2-x)^2/4 := by nlinarith [sq_nonneg (y-(1/2-x-y))]
  have hs : (1/2-x)^2 ≤ (1/2-a)^2 := by
    have ha : a ≤ 1/2 := hx.1.trans hxhi
    nlinarith [hx.1]
  have h1 := mul_le_mul_of_nonneg_left hquad hx0
  have h2 := mul_le_mul hx.2 (div_le_div_of_nonneg_right hs (by norm_num : (0:ℝ) ≤ 4))
    (by positivity : (0:ℝ) ≤ (1/2-x)^2/4) (hp.1.le.trans hp.2.1)
  unfold D
  nlinarith only [h1,h2]

theorem poly_lower {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b v) :
    poly x y ≤ uniformKernel (1/1000) (x,y) := by
  have hp := parameters
  have hy0 : 0 ≤ y := (hp.1.le.trans hp.2.1).trans hy.1
  have ha : 0 < a := hp.1
  have hA : 0 < A := hp.2.2.2.2.2
  have hD : 0 < D := hp.2.2.2.2.1
  have hUL : 0 < U-L := sub_pos.mpr hp.2.2.2.1
  have hK := uniform_nonneg (by norm_num : (0:ℝ) ≤ 1/1000) (x,y)
  by_cases hs : x+y ≤ U
  · have hr : truncatedSixthLowerAdmissibleRegion (1/1000) x y := by
      refine ⟨⟨hx.1,hx.2,hy.1,?_,hs⟩,hy.2⟩
      have h := hy.2
      norm_num [v,truncatedSixthLowerSigma,truncatedSixthLowerAlpha] at *
      linarith
    have hd := denominator_pos (by norm_num : (0:ℝ) ≤ 0)
      (region_mono (by norm_num : (0:ℝ) ≤ 1/1000) hr)
    have hz : 0 ≤ 1/2-x-y := by
      have ha := hp.1
      unfold U at hs
      linarith
    by_cases ht : L ≤ x+y
    · have hn : 0 ≤ (x+y-L)/(750*a) := div_nonneg (by linarith) (by positivity)
      have hseed : seed (truncatedSixthLowerS 0 x y) = (x+y-L)/(750*a) := by
        unfold seed truncatedSixthLowerS truncatedSixthLowerC
        have he : (7/2-(1/2-0-x-y)/truncatedSixthLowerAlpha)/750 =
            (x+y-L)/(750*a) := by
          unfold L a
          field_simp [ne_of_gt truncatedSixthLower_parameters.1]
          ring
        rw [he, max_eq_right hn]
      rw [uniformKernel, if_pos hr, hseed]
      have hcap := denom_cap hx hz hy0
      have hdiv : ((x+y-L)/(750*a))/D ≤
          ((x+y-L)/(750*a))/(x*y*(truncatedSixthLowerC 0-x-y)) := by
        exact div_le_div_of_nonneg_left hn hd (by simpa [truncatedSixthLowerC] using hcap)
      apply le_trans _ hdiv
      have htU : U-x-y ≤ U-L := by linarith
      have hmul := mul_le_mul_of_nonneg_left htU
        (mul_nonneg hA.le (sub_nonneg.mpr ht))
      have he : A*(x+y-L)*(U-L) = ((x+y-L)/(750*a))/D := by
        unfold A
        field_simp [ne_of_gt ha,ne_of_gt hD,ne_of_gt hUL]
      unfold poly
      nlinarith only [hmul,he]
    · have hprod : poly x y ≤ 0 := by
        unfold poly
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hp.2.2.2.2.2.le (by linarith)) (by linarith)
      exact hprod.trans hK
  · have ht : L ≤ x+y := by linarith [hp.2.2.2.1]
    have hprod : poly x y ≤ 0 := by
      unfold poly
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hA.le (sub_nonneg.mpr ht)) (by linarith)
    exact hprod.trans hK

/-- A universal FTC identity, not numerical quadrature. -/
theorem quadratic_integral (p q r l u : ℝ) :
    (∫ t in l..u, p*t^2+q*t+r) =
      (p*u^3/3+q*u^2/2+r*u)-(p*l^3/3+q*l^2/2+r*l) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    convert ((((hasDerivAt_id t).pow 3).const_mul p |>.div_const 3).add
      (((hasDerivAt_id t).pow 2).const_mul q |>.div_const 2)).add
      ((hasDerivAt_id t).const_mul r) using 1
    · ext z
      dsimp
    · dsimp
      ring
  · exact (by fun_prop : Continuous (fun t : ℝ => p*t^2+q*t+r)).intervalIntegrable _ _

def p0 : ℝ := -(v-b)
def p1 : ℝ := (U+L)*(v-b)-(v^2-b^2)
def p2 : ℝ := (U+L)*(v^2-b^2)/2-(v^3-b^3)/3-L*U*(v-b)
def moment : ℝ := (p0*b^3/3+p1*b^2/2+p2*b)-(p0*a^3/3+p1*a^2/2+p2*a)
def polynomialPayment : ℝ := 4*A*moment

theorem inner_integral (x : ℝ) :
    (∫ y in b..v, poly x y) = A*(p0*x^2+p1*x+p2) := by
  have he : (fun y : ℝ => poly x y) =
      (fun y => A*((-1)*y^2+(U+L-2*x)*y+(-x^2+(U+L)*x-L*U))) := by
    funext y; unfold poly; ring
  rw [he,intervalIntegral.integral_const_mul,quadratic_integral]
  unfold p0 p1 p2
  ring

theorem iterated_integral :
    (∫ x in a..b, ∫ y in b..v, poly x y) = A*moment := by
  simp_rw [inner_integral]
  rw [intervalIntegral.integral_const_mul,quadratic_integral]
  rfl

theorem poly_integrable : IntegrableOn (fun z : ℝ × ℝ => poly z.1 z.2) R := by
  exact (by unfold poly; fun_prop : Continuous (fun z : ℝ × ℝ => poly z.1 z.2)).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

theorem rectangle_integral : (∫ z in R, poly z.1 z.2) = A*moment := by
  have hi := poly_integrable
  unfold R at hi ⊢
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod _ hi]
  simp_rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le parameters.2.1]
  simp_rw [← intervalIntegral.integral_of_le parameters.2.2.1]
  exact iterated_integral

theorem polynomial_payment : polynomialPayment ≤ Gamma6 := by
  have hi := uniform_integrable (by norm_num : (0:ℝ) < 1/1000) le_rfl
  have hsub := setIntegral_mono_on poly_integrable hi.integrableOn
    (measurableSet_Icc.prod measurableSet_Icc)
    (fun z hz => poly_lower hz.1 hz.2)
  have hwhole := setIntegral_le_integral (s := R) hi
    (Filter.Eventually.of_forall (uniform_nonneg (by norm_num : (0:ℝ) ≤ 1/1000)))
  rw [rectangle_integral] at hsub
  have h := mul_le_mul_of_nonneg_left (hsub.trans hwhole) (by norm_num : (0:ℝ) ≤ 4)
  simpa only [Gamma6,FullAdmissibleSeed.Gamma,polynomialPayment,mul_assoc] using h

theorem polynomial_payment_exact : polynomialPayment =
    47697773811357812609179/46058903755654901562500000 := by
  norm_num [polynomialPayment,moment,p0,p1,p2,A,D,L,U,v,a,b,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

/-- Explicit magnitude from the whole-mask certificate, not the old small rectangle. -/
theorem gamma6_magnitude : (1/1000:ℝ) < Gamma6 := by
  have h := polynomial_payment
  rw [polynomial_payment_exact] at h
  linarith

theorem replacement_increment : (225/1000000:ℝ) < (Gamma6-47/481250)/4 := by
  have h := gamma6_magnitude
  linarith

end
end Wu2008DoubleSieve.FullAdmissibleStrength
