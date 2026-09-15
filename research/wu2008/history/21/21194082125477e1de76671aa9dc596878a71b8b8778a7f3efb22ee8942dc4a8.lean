import E05SixthMajorEnvelope

noncomputable section
open Real Set MeasureTheory
open Wu2008DoubleSieve
open Wu2008DoubleSieve.PositiveSixthFTC
open Wu2008DoubleSieve.DynamicSixthEnvelope
open Wu2008DoubleSieve.SharpLogRecurrence
open Wu2008DoubleSieve.SharpMassBalance
open scoped Interval

namespace WuTarget.E05SixthMajor

def innerRate : ℝ := (69/50)*(1/innerDenom1+1/innerDenom2)
def innerCorrection (x : ℝ) : ℝ := innerRate*(lam-x-b)^5
def innerCredit : ℝ := (2/3)*innerRate*((lam-a-b)^6-(lam-2*b)^6)

theorem ratio_fifth (u v x : ℝ) (hv : v ≠ 0) :
    E05Sixth.fifthLogTerm (u/v)/x = (2/5)*((u-v)^5/(x*(u+v)^5)) := by
  have hn : u/v-1 = (u-v)/v := by field_simp
  have hd : u/v+1 = (u+v)/v := by field_simp
  unfold E05Sixth.fifthLogTerm
  rw [hn,hd,div_div_div_cancel_right₀ hv,div_pow]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem inner_denominators {x : ℝ} (hx : x ∈ Icc a b) :
    x*(1/2-x-b+2*a)^5 ≤ innerDenom1 ∧
    x*(1/2-x-2*a+b)^5 ≤ innerDenom2 := by
  have hg := Phase25.outer_geometry hx
  have h1 : x ≤ 1/2-b+2*a := by linarith [hg.2.2.1,geometry.1]
  have h2 : x ≤ 1/2-2*a+b := by linarith [hg.2.2.2.1,geometry.2.2.1]
  have e1 : (1/2:ℝ)-b+2*a-x = 1/2-x-b+2*a := by ring
  have e2 : (1/2:ℝ)-2*a+b-x = 1/2-x-2*a+b := by ring
  constructor
  · simpa only [innerDenom1,e1] using fifth_product_max hg.1.le h1
  · simpa only [innerDenom2,e2] using fifth_product_max hg.1.le h2

theorem inner_correction_le_gaps {x : ℝ} (hx : x ∈ Icc a b) :
    innerCorrection x ≤
      Phase25.S (1/2-x) (2*a)*
        (E05Sixth.fifthLogTerm ((1/2-x-b)/(2*a))+
          E05Sixth.fifthLogTerm ((1/2-x-2*a)/b))/x := by
  have hg := Phase25.outer_geometry hx
  have h1 : 0 < 1/2-x-b+2*a := by linarith [hg.2.2.1,geometry.1]
  have h2 : 0 < 1/2-x-2*a+b := by linarith [hg.2.2.2.1,geometry.2.2.1]
  have hw : 0 ≤ lam-x-b := by linarith [(moving_geometry hx).1]
  have hh1 := div_le_div_of_nonneg_left (pow_nonneg hw 5)
    (mul_pos hg.1 (pow_pos h1 5)) (inner_denominators hx).1
  have hh2 := div_le_div_of_nonneg_left (pow_nonneg hw 5)
    (mul_pos hg.1 (pow_pos h2 5)) (inner_denominators hx).2
  have he1 :
      E05Sixth.fifthLogTerm ((1/2-x-b)/(2*a))/x =
        (2/5)*((lam-x-b)^5/(x*(1/2-x-b+2*a)^5)) := by
    rw [ratio_fifth _ _ _ (mul_ne_zero (by norm_num) geometry.1.ne')]
    have he : (1/2:ℝ)-x-b-2*a = lam-x-b := by unfold lam; ring
    rw [he]
  have he2 :
      E05Sixth.fifthLogTerm ((1/2-x-2*a)/b)/x =
        (2/5)*((lam-x-b)^5/(x*(1/2-x-2*a+b)^5)) := by
    rw [ratio_fifth _ _ _ geometry.2.2.1.ne']
    have he : (1/2:ℝ)-x-2*a-b = lam-x-b := by unfold lam; ring
    rw [he]
  rw [mul_div_assoc,add_div,he1,he2]
  have hn : 0 ≤ (lam-x-b)^5/(x*(1/2-x-b+2*a)^5)+
      (lam-x-b)^5/(x*(1/2-x-2*a+b)^5) :=
    add_nonneg (div_nonneg (pow_nonneg hw 5) (mul_pos hg.1 (pow_pos h1 5)).le)
      (div_nonneg (pow_nonneg hw 5) (mul_pos hg.1 (pow_pos h2 5)).le)
  have hp := mul_le_mul_of_nonneg_right (S_lower hx) hn
  have hq := mul_le_mul_of_nonneg_left (add_le_add hh1 hh2)
    (show (0:ℝ) ≤ 69/50 by norm_num)
  unfold innerCorrection innerRate
  simp only [div_eq_mul_inv] at hp hq ⊢
  nlinarith only [hp,hq]

theorem inner_correction_paid {x : ℝ} (hx : x ∈ Icc a b) :
    Phase25.rationalInner (1/2-x)+innerCorrection x ≤ Phase25.movingExact x := by
  have hg := Phase25.outer_geometry hx
  have h1 : 1 ≤ (1/2-x-b)/(2*a) :=
    (le_div_iff₀ (mul_pos (by norm_num) geometry.1)).mpr (by linarith [hg.2.2.2.2])
  have h2 : 1 ≤ (1/2-x-2*a)/b :=
    (le_div_iff₀ geometry.2.2.1).mpr (by linarith [hg.2.2.2.2])
  have hs := Phase25.S_pos (h := 2*a) hg.2.1 (by linarith [hg.2.2.2.1])
  have hp := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (add_le_add (E05Sixth.log_fifth_lower h1) (E05Sixth.log_fifth_lower h2)) hs.le)
    hg.1.le
  have hgap := inner_correction_le_gaps hx
  rw [Phase25.movingExact_endpoint,
    Phase25.endpoint_difference hg.2.2.1 hg.2.2.2.1]
  unfold Phase25.rationalInner
  have he : (1/2:ℝ)-(1/2-x) = x := by ring
  rw [he]
  simp only [add_div,mul_add] at hp hgap ⊢
  linarith only [hp,hgap]

theorem inner_correction_ftc :
    (4*∫ x in a..b, innerCorrection x) = innerCredit := by
  have hd (x : ℝ) (_hx : x ∈ uIcc a b) :
      HasDerivAt (fun x : ℝ => -(innerRate/6)*(lam-x-b)^6) (innerCorrection x) x := by
    convert (((((hasDerivAt_const x lam).sub (hasDerivAt_id x)).sub_const b).pow 6).const_mul
      (-(innerRate/6))) using 1 <;>
      first | rfl | (dsimp [innerCorrection]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by unfold innerCorrection; fun_prop :
      Continuous innerCorrection).intervalIntegrable a b)]
  unfold innerCredit
  have he : lam-b-b = lam-2*b := by ring
  rw [he]
  ring

end WuTarget.E05SixthMajor
