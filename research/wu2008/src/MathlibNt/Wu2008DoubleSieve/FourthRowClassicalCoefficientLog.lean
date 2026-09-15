import MathlibNt.Wu2008DoubleSieve.FourthRowClassicalCoefficientTriangle

namespace Wu2008DoubleSieve
open Set MeasureTheory Real
open scoped Interval

theorem fourthRowClassical_log_continuous :
    ContinuousOn (fun v : ℝ => log (v - 1) / v) (Ioi 1) := by
  apply ((continuousOn_id.sub continuousOn_const).log (fun v hv => by
    exact ne_of_gt (sub_pos.mpr hv))).div continuousOn_id
  intro v hv
  exact ne_of_gt (lt_trans (by norm_num) hv)

theorem fourthRowClassical_L_integrable {x : ℝ} (hx : 2 < x) :
    IntervalIntegrable (fun v : ℝ => log (v - 1) / v) volume 2 (x - 1) := by
  apply (fourthRowClassical_log_continuous.mono _).intervalIntegrable
  intro v hv
  exact lt_of_lt_of_le (lt_min (by norm_num) (by linarith : (1 : ℝ) < x - 1)) hv.1

theorem fourthRowClassical_L_sub {A B : ℝ} (hA : 2 < A) (hB : 2 < B) :
    fourthRowClassicalL A - fourthRowClassicalL B =
      ∫ v in (B - 1)..(A - 1), log (v - 1) / v := by
  exact intervalIntegral.integral_interval_sub_left
    (fourthRowClassical_L_integrable hA) (fourthRowClassical_L_integrable hB)

theorem fourthRowClassical_reciprocal {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1 / 2) :
    (∫ u in a..b, log (1 / u - 2) / (u * (1 - u))) =
      ∫ v in (1 / b - 1)..(1 / a - 1), log (v - 1) / v := by
  have hp (u : ℝ) (hu : u ∈ uIcc a b) : 0 < u ∧ u < 1 / 2 := by
    rw [uIcc_of_le hab] at hu
    exact ⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩
  have hd (u : ℝ) (hu : u ∈ uIcc a b) :
      HasDerivAt (fun x : ℝ => 1 / x - 1) (-(1 / u ^ 2)) u := by
    simpa only [one_div, neg_div, one_mul, Pi.inv_apply, id_eq] using
      ((hasDerivAt_id u).inv (hp u hu).1.ne').sub_const 1
  have hc : ContinuousOn (fun u : ℝ => -(1 / u ^ 2)) (uIcc a b) := by
    apply (continuousOn_const.div (continuousOn_id.pow 2) _).neg
    intro u hu
    exact pow_ne_zero _ (hp u hu).1.ne'
  have hg : ContinuousOn (fun v : ℝ => log (v - 1) / v)
      ((fun x : ℝ => 1 / x - 1) '' uIcc a b) := by
    apply fourthRowClassical_log_continuous.mono
    rintro _ ⟨u, hu, rfl⟩
    change 1 < 1 / u - 1
    have hh := (lt_div_iff₀ (hp u hu).1).mpr (show 2 * u < 1 by linarith [(hp u hu).2])
    linarith
  have hs := intervalIntegral.integral_comp_mul_deriv' hd hc hg
  have he : (∫ u in a..b,
      ((fun v : ℝ => log (v - 1) / v) ∘ (fun x => 1 / x - 1)) u * -(1 / u ^ 2)) =
      -(∫ u in a..b, log (1 / u - 2) / (u * (1 - u))) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp
    rw [show 1 / u - 1 - 1 = 1 / u - 2 by ring]
    have hu0 := (hp u hu).1.ne'
    have hu1 : 1 - u ≠ 0 := by linarith [(hp u hu).2]
    field_simp [hu0, hu1]
  rw [he, intervalIntegral.integral_symm (a := 1 / b - 1) (b := 1 / a - 1)] at hs
  exact neg_injective hs

theorem fourthRowClassical_log_parts_integrable {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1 / 2) :
    IntervalIntegrable (fun u : ℝ => log ((1 - u - a) / a) / (u * (1 - u))) volume a b ∧
    IntervalIntegrable (fun u : ℝ => log (1 / u - 2) / (u * (1 - u))) volume a b := by
  have hp (u : ℝ) (hu : u ∈ uIcc a b) : 0 < u ∧ u < 1 / 2 := by
    rw [uIcc_of_le hab] at hu
    exact ⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩
  have hw : ContinuousOn (fun u : ℝ => u * (1 - u)) (uIcc a b) := by fun_prop
  have hn (u : ℝ) (hu : u ∈ uIcc a b) : u * (1 - u) ≠ 0 :=
    mul_ne_zero (hp u hu).1.ne' (ne_of_gt (by linarith [(hp u hu).2]))
  constructor
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div _ hw hn
    apply ContinuousOn.log
      (((continuousOn_const.sub continuousOn_id).sub continuousOn_const).div_const a)
    intro u hu
    apply ne_of_gt
    apply div_pos _ ha
    change 0 < 1 - u - a
    have hu' := hp u hu
    linarith
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div _ hw hn
    apply ContinuousOn.log
      ((continuousOn_const.div continuousOn_id (fun u hu => (hp u hu).1.ne')).sub continuousOn_const)
    intro u hu
    apply ne_of_gt
    exact sub_pos.mpr ((lt_div_iff₀ (hp u hu).1).mpr (by linarith [(hp u hu).2]))

theorem fourthRowClassical_J_positive_arguments {A B u : ℝ}
    (hAB : B ≤ A) (hB : 2 < B)
    (hu : u ∈ Icc (1 - 1 / B) (1 - 1 / A)) :
    0 < u ∧ 0 < 1 - u ∧ 0 < A * u - 1 := by
  have hA : 2 < A := hB.trans_le hAB
  have hAi : 0 < 1 / A := one_div_pos.mpr (by linarith)
  have hBi : 1 / B < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hB
  have hu0 : 0 < u := by linarith [hu.1]
  have hm := mul_lt_mul_of_pos_right hA hu0
  exact ⟨hu0, by linarith [hu.2], by linarith [hu.1]⟩

theorem fourthRowClassical_J_integrable {A B : ℝ} (hAB : B ≤ A) (hB : 2 < B) :
    IntervalIntegrable (fun u : ℝ => log (A * u - 1) / (u * (1 - u))) volume
      (1 - 1 / B) (1 - 1 / A) := by
  have hab : 1 - 1 / B ≤ 1 - 1 / A :=
    sub_le_sub_left (one_div_le_one_div_of_le (by linarith : 0 < B) hAB) 1
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply ContinuousOn.log
      ((continuousOn_const.mul continuousOn_id).sub continuousOn_const)
    intro u hu
    exact (fourthRowClassical_J_positive_arguments hAB hB hu).2.2.ne'
  · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  · intro u hu
    have hp := fourthRowClassical_J_positive_arguments hAB hB hu
    exact mul_ne_zero hp.1.ne' hp.2.1.ne'

theorem fourthRowClassical_equal_endpoints (A : ℝ) :
    fourthRowClassicalTriangle A A = 0 ∧ fourthRowClassicalJ A A = 0 := by
  simp [fourthRowClassicalTriangle, fourthRowClassicalJ]

theorem fourthRowClassical_triangle_eq_log {A B : ℝ}
    (hAB : B ≤ A) (hB : 2 < B) :
    fourthRowClassicalTriangle A B = fourthRowClassicalJ B A -
      (fourthRowClassicalL A - fourthRowClassicalL B) := by
  have hA : 2 < A := hB.trans_le hAB
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have ha : 0 < 1 / A := one_div_pos.mpr hA0
  have hab : 1 / A ≤ 1 / B := one_div_le_one_div_of_le hB0 hAB
  have hb : 1 / B < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hB
  have hparts := fourthRowClassical_log_parts_integrable ha hab hb
  unfold fourthRowClassicalTriangle
  rw [(fourthRowClassical_triangle_fubini ha hab hb).2.2]
  calc
    _ = ∫ u in (1 / A)..(1 / B),
        (log ((1 - u - 1 / A) / (1 / A)) - log (1 / u - 2)) / (u * (1 - u)) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hab]
      intro u hu
      exact fourthRowClassical_inner_log ha hu.1 (hu.2.trans_lt hb)
    _ = (∫ u in (1 / A)..(1 / B), log ((1 - u - 1 / A) / (1 / A)) / (u * (1 - u))) -
        ∫ u in (1 / A)..(1 / B), log (1 / u - 2) / (u * (1 - u)) := by
      rw [← intervalIntegral.integral_sub hparts.1 hparts.2]
      apply intervalIntegral.integral_congr
      intro u _
      exact sub_div _ _ _
    _ = fourthRowClassicalJ B A - (fourthRowClassicalL A - fourthRowClassicalL B) := by
      congr 1
      · unfold fourthRowClassicalJ
        rw [← intervalIntegral.integral_comp_sub_left (fun u : ℝ => log (A * u - 1) / (u * (1 - u))) 1]
        apply intervalIntegral.integral_congr
        intro u _
        dsimp
        congr 1
        · congr 1
          field_simp [hA0.ne']
        · ring
      · rw [fourthRowClassical_reciprocal ha hab hb, fourthRowClassical_L_sub hA hB]
        simp only [one_div_one_div]

end Wu2008DoubleSieve
