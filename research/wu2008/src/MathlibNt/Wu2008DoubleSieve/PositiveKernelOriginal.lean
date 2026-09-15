import MathlibNt.Wu2008DoubleSieve.PositiveKernelAnchor

namespace Wu2008DoubleSieve
open Set MeasureTheory Real
open scoped Interval

/-- Positive denominators on the original transformed J interval. -/
theorem positiveKernel_J_domain {a b t : ℝ} (ha : 2 < a) (_hab : a ≤ b)
    (ht : t ∈ Icc a b) : 0 < t ∧ 0 < t-1 ∧ 0 < (b-1)*t-b := by
  have ht2 : 2 < t := ha.trans_le ht.1
  have ht1 : 0 < t-1 := by linarith
  have hh := mul_le_mul_of_nonneg_right ht.2 ht1.le
  have hp := mul_pos (show 0 < t by linarith) (show 0 < t-2 by linarith)
  exact ⟨by linarith, ht1, by nlinarith⟩

/-- A true change of variables in the imported original J, not a new definition. -/
theorem positiveKernel_J_transform {a b : ℝ} (ha : 2 < a) (hab : a ≤ b) :
    fourthRowClassicalJ a b =
      ∫ t in a..b, log (b-1-b/t)/(t-1) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hp (t : ℝ) (ht : t ∈ uIcc a b) :=
    positiveKernel_J_domain ha hab (by rwa [uIcc_of_le hab] at ht)
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => 1-1/t) (1/t^2) t := by
    simpa only [one_div, neg_div, neg_neg, Pi.inv_apply, id_eq] using
      ((hasDerivAt_id t).inv (hp t ht).1.ne').const_sub 1
  have hc : ContinuousOn (fun t : ℝ => 1/t^2) (uIcc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero _ (hp t ht).1.ne')
  have hm : MapsTo (fun t : ℝ => 1-1/t) (uIcc a b)
      (Icc (1-1/a) (1-1/b)) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact ⟨sub_le_sub_left (one_div_le_one_div_of_le ha0 ht.1) 1,
      sub_le_sub_left (one_div_le_one_div_of_le (ha0.trans_le ht.1) ht.2) 1⟩
  have hg : ContinuousOn (fun u : ℝ => log (b*u-1)/(u*(1-u)))
      ((fun t : ℝ => 1-1/t) '' uIcc a b) := by
    have hp' (u : ℝ) (hu : u ∈ ((fun t : ℝ => 1-1/t) '' uIcc a b)) :
        0 < u ∧ 0 < 1-u ∧ 0 < b*u-1 := by
      rcases hu with ⟨t, ht, rfl⟩
      exact fourthRowClassical_J_positive_arguments hab ha (hm ht)
    apply ContinuousOn.div
      (((continuousOn_const.mul continuousOn_id).sub continuousOn_const).log
        (fun u hu => (hp' u hu).2.2.ne'))
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      (fun u hu => mul_ne_zero (hp' u hu).1.ne' (hp' u hu).2.1.ne')
  have he := intervalIntegral.integral_comp_mul_deriv' hd hc hg
  change _ = fourthRowClassicalJ a b at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp
  have hp' := hp t ht
  have hlog : b*(1-1/t)-1 = b-1-b/t := by ring
  rw [hlog]
  field_simp [hp'.1.ne', hp'.2.1.ne']
  ring

/-- The signed endpoint b=3 is exactly the negative anchor. -/
theorem positiveKernel_original_anchor {a : ℝ} (ha : 2 < a) (ha3 : a < 3) :
    fourthRowClassicalJ a 3 - 2*fourthRowClassicalL 3 =
      -(∫ z in (0 : ℝ)..(3-a), log ((3-z)/(3-2*z))/(2-z)) := by
  rw [positiveKernel_J_transform ha ha3.le]
  have hL : fourthRowClassicalL 3 = 0 := by
    norm_num [fourthRowClassicalL]
  rw [hL, mul_zero, sub_zero]
  have href := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => log (3-1-3/t)/(t-1)) 3 (a := 0) (b := 3-a)
  simp only [sub_zero, sub_sub_cancel] at href
  rw [← href]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ 3-a)] at hz
  have hz1 : z < 1 := by linarith [hz.2]
  have h3 : 3-z ≠ 0 := by linarith
  have h32 : 3-2*z ≠ 0 := by linarith
  have hlog : 3-1-3/(3-z) = ((3-z)/(3-2*z))⁻¹ := by
    field_simp [h3, h32, show 3-z*2 ≠ 0 by linarith]
    ring
  dsimp
  rw [hlog, log_inv]
  ring

/-- A strict rational bound for the literal original functional at the included endpoint. -/
theorem positiveKernel_original_anchor_lower {a : ℝ} (ha : 2 < a) (ha3 : a < 3) :
    -(3-a)^2 * (1/36 + 1/(3*(2*a-3)*(a-1))) <
      fourthRowClassicalJ a 3 - 2*fourthRowClassicalL 3 := by
  rw [positiveKernel_original_anchor ha ha3]
  have h := positiveKernel_anchor_payment (h := 3-a) (by linarith) (by linarith)
  have h1 : 3-2*(3-a) = 2*a-3 := by ring
  have h2 : 2-(3-a) = a-1 := by ring
  rw [h1, h2] at h
  linarith

end Wu2008DoubleSieve
