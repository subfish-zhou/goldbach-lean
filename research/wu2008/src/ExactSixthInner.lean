import MathlibNt.Wu2008DoubleSieve.SixthLogCubicPayment

namespace Wu2008DoubleSieve.Phase25
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope
open scoped Interval
noncomputable section

def S (c h : ℝ) : ℝ := (8/3)/c-4*h/c^2+2*h^2/c^3-(2/3)*h^3/c^4
def T2 (c h : ℝ) : ℝ := -4*h/c+2*h^2/c^2-(2/3)*h^3/c^3
def T3 (c h : ℝ) : ℝ := 2*h^2/c-(2/3)*h^3/c^2
def T4 (c h : ℝ) : ℝ := -(2/3)*h^3/c
def g (h z : ℝ) : ℝ := (8/3)/z-4*h/z^2+2*h^2/z^3-(2/3)*h^3/z^4
def P (c h z : ℝ) : ℝ := S c h*(log z-log (c-z))-
  T2 c h*z⁻¹-(T3 c h/2)*(z⁻¹)^2-(T4 c h/3)*(z⁻¹)^3

theorem S_factor {c h : ℝ} (hc : c ≠ 0) :
    S c h = (2/3)*(c-h)*((c-h)^2+3*c^2)/c^4 := by
  unfold S
  field_simp [hc]
  ring

theorem S_pos {c h : ℝ} (hc : 0 < c) (hh : h < c) : 0 < S c h := by
  rw [S_factor hc.ne']
  exact div_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hh))
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (by norm_num) (sq_pos_of_pos hc))))
    (pow_pos hc 4)

theorem partial_fractions {c h z : ℝ} (hc : c ≠ 0) (hz : z ≠ 0)
    (hcz : c-z ≠ 0) :
    S c h*(1/z+1/(c-z))+T2 c h/z^2+T3 c h/z^3+T4 c h/z^4 =
      g h z/(c-z) := by
  unfold S T2 T3 T4 g
  field_simp [hc,hz,hcz]
  ring

theorem P_derivative {c h z : ℝ} (hc : c ≠ 0) (hz : z ≠ 0)
    (hcz : c-z ≠ 0) : HasDerivAt (P c h) (g h z/(c-z)) z := by
  rw [← partial_fractions hc hz hcz]
  have hi := hasDerivAt_id z
  have hd := (hasDerivAt_const z c).sub hi
  have hv := hi.inv hz
  have hh := (((((hasDerivAt_log hz).sub (hd.log hcz)).const_mul (S c h)).sub
    (hv.const_mul (T2 c h))).sub ((hv.pow 2).const_mul (T3 c h/2))).sub
    ((hv.pow 3).const_mul (T4 c h/3))
  convert hh using 1 <;> first | rfl | (dsimp; field_simp; ring)

def exactKernel (x y : ℝ) : ℝ :=
  (2*(lam-x-y)/(1/2-x-y)^2+(2/3)*(lam-x-y)^3/(1/2-x-y)^4)/(x*y)
def innerPrimitive (x y : ℝ) : ℝ := -P (1/2-x) (2*a) (1/2-x-y)/x

theorem kernel_identity {x y : ℝ} (hy : y ≠ 0) (_hz : 1/2-x-y ≠ 0) :
    exactKernel x y = g (2*a) (1/2-x-y)/((1/2-x-(1/2-x-y))*x) := by
  unfold exactKernel g lam
  field_simp [hy]
  ring

theorem inner_derivative {x y : ℝ} (hx : x ≠ 0) (hc : 1/2-x ≠ 0)
    (hy : y ≠ 0) (hz : 1/2-x-y ≠ 0) :
    HasDerivAt (innerPrimitive x) (exactKernel x y) y := by
  have hcy : 1/2-x-(1/2-x-y) ≠ 0 := by convert hy using 1; ring
  have hp := ((P_derivative (h := 2*a) hc hz hcy).comp y
    ((hasDerivAt_const y (1/2-x)).sub (hasDerivAt_id y))).neg.div_const x
  rw [kernel_identity hy hz]
  convert hp using 1 <;> first | rfl | (field_simp; ring)

theorem mask_geometry {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (lam-x)) :
    0 < x ∧ 0 < y ∧ 0 < 1/2-x ∧ 0 < 1/2-x-y ∧ 2*a ≤ 1/2-x-y := by
  have ha := geometry.1
  have hb := geometry.2.2.1
  have hyp := hb.trans_le hy.1
  have hu : y ≤ 1/2-2*a-x := hy.2
  exact ⟨ha.trans_le hx.1,hb.trans_le hy.1,by linarith,by linarith,by linarith⟩

theorem retained_exact_lower {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    exactKernel x y ≤ truncatedSixthZeroDeltaRegular 0 (x,y) := by
  have hp := truncatedSixthLower_parameters
  have hys := hy.2.trans (moving_geometry hx).2
  have hr : truncatedSixthLowerRegion 0 x y := by
    refine ⟨hx.1,hx.2,hy.1,hys,?_⟩
    dsimp [truncatedSixthLowerC]
    have hd : y ≤ 1/2-2*a-x := hy.2
    linarith
  have hb := truncatedSixthLower_region_bounds (by norm_num : (0 : ℝ) ≤ 0) hr
  have hz := (mask_geometry hx hy).2.2.2.1
  have hu : 2 ≤ truncatedSixthLowerS 0 x y := hb.2.2.2.1
  have hl := (log_lower (t := truncatedSixthLowerS 0 x y-1) (by linarith)).trans (lower_ge_log hu)
  have hdiv := div_le_div_of_nonneg_right hl (mul_pos (mul_pos hb.1 hb.2.1) hz).le
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx ⟨hy.1,hys⟩,if_pos hr]
  simp only [truncatedSixthLowerC,sub_zero]
  change _ ≤ wuLowerCoefficient (truncatedSixthLowerS 0 x y)/(x*y*(1/2-x-y))
  calc
    _ = lowerLog (truncatedSixthLowerS 0 x y-1)/(x*y*(1/2-x-y)) := by
      have hz' : 1-x*2-y*2 ≠ 0 := by linarith
      simp only [exactKernel,lowerLog,truncatedSixthLowerS,truncatedSixthLowerC,lam,sub_zero]
      field_simp [hp.1.ne',hb.1.ne',hb.2.1.ne',hz.ne',hz']
      ring
    _ ≤ _ := hdiv

theorem inner_integrable {x : ℝ} (hx : x ∈ Icc a b) :
    IntervalIntegrable (exactKernel x) volume b (lam-x) := by
  apply ContinuousOn.intervalIntegrable
  have hn (y : ℝ) (hy : y ∈ uIcc b (lam-x)) :=
    mask_geometry hx (uIcc_of_le (moving_geometry hx).1 ▸ hy)
  have hz : ContinuousOn (fun y : ℝ => (1/2-x-y)⁻¹) (uIcc b (lam-x)) :=
    (continuousOn_const.sub continuousOn_id).inv₀ (fun y hy => (hn y hy).2.2.2.1.ne')
  have hy : ContinuousOn (fun y : ℝ => y⁻¹) (uIcc b (lam-x)) :=
    continuousOn_id.inv₀ (fun y hy => (hn y hy).2.1.ne')
  unfold exactKernel
  simp only [div_eq_mul_inv,mul_inv_rev,← inv_pow]
  fun_prop

def movingExact (x : ℝ) : ℝ := innerPrimitive x (lam-x)-innerPrimitive x b

theorem inner_ftc {x : ℝ} (hx : x ∈ Icc a b) :
    (∫ y in b..lam-x, exactKernel x y) = movingExact x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (inner_integrable hx)
  intro y hy
  have hg := mask_geometry hx (uIcc_of_le (moving_geometry hx).1 ▸ hy)
  exact inner_derivative hg.1.ne' hg.2.2.1.ne' hg.2.1.ne' hg.2.2.2.1.ne'

end
end Wu2008DoubleSieve.Phase25
