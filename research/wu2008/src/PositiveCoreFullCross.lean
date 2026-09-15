import FeedbackP2

namespace PositiveCoreResume
open Wu2008DoubleSieve Set MeasureTheory Real
open scoped Interval
noncomputable section

/-- Full supporting interval, not the midpoint rectangle used by BaseHCross. -/
theorem linear_tail (a b : ℝ) (_hab : a ≤ b) :
    (∫ u in a..b, b-u) = (b-a)^2/2 := by
  have hd : ∀ u : ℝ, HasDerivAt (fun v : ℝ => -(b-v)^2/2) (b-u) u := by
    intro u
    convert! (((hasDerivAt_const u b).sub (hasDerivAt_id u)).pow 2).neg.div_const 2 using 1 ; dsimp only [Pi.sub_apply, id_eq] ; ring
  have hi : IntervalIntegrable (fun u : ℝ => b-u) volume a b :=
    (continuous_const.sub continuous_id).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi
  convert h using 1 ; ring

/-- Exact FTC on the full quadratic cross profile. -/
theorem quadratic_tail (a b : ℝ) :
    (∫ u in a..b, (b-u)^2) = (b-a)^3/3 := by
  have hd : ∀ u : ℝ, HasDerivAt (fun v : ℝ => -(b-v)^3/3) ((b-u)^2) u := by
    intro u
    convert! (((hasDerivAt_const u b).sub (hasDerivAt_id u)).pow 3).neg.div_const 3 using 1 ; dsimp only [Pi.sub_apply, id_eq] ; ring
  have hi : IntervalIntegrable (fun u : ℝ => (b-u)^2) volume a b :=
    ((continuous_const.sub continuous_id).pow 2).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi
  convert h using 1 ; ring

/-- Same actual H, same delta; only positive cross mass formerly discarded is restored. -/
theorem H_full_cross {δ s : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hs : 3 ≤ s) (ht : s ≤ 9/2) :
    (9/2-s)^2/5250 ≤ wuImprovementLimit true δ s := by
  have hab : s-1 ≤ 7/2 := by linarith
  have hi := wuImprovementLimit_div_intervalIntegrable false hδ
    (by linarith : δ < 1/2) (by linarith : 1 ≤ s-1) hab (by norm_num : (7/2 : ℝ) ≤ 10)
  have hm : (∫ u in (s-1)..(7/2 : ℝ), (7/2-u)/2625) ≤
      ∫ u in (s-1)..(7/2 : ℝ), wuImprovementLimit false δ u/u := by
    apply intervalIntegral.integral_mono_on hab
      (((continuous_const.sub continuous_id).div_const 2625).intervalIntegrable _ _) hi
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hl : (7/2-u)/750 ≤ wuImprovementLimit false δ u := by
      by_cases he : u < 7/2
      · exact (SecondFunctionalSmallDelta.h_strict hδ hd (by linarith [hu.1]) he).le
      · have heq : u = 7/2 := by linarith [hu.2]
        rw [heq]; norm_num only [sub_self, zero_div]
        exact wuImprovementLimit_nonneg false hδ (by linarith) (by norm_num) (by norm_num)
    apply (le_div_iff₀ hu0).mpr
    have hh := mul_nonneg (show 0 ≤ 7/2-u by linarith [hu.2])
      (show 0 ≤ 7/2-u by linarith [hu.2])
    dsimp only [Pi.sub_apply, Pi.pow_apply, id_eq] at *
    nlinarith only [hl, hh]
  rw [intervalIntegral.integral_div, linear_tail _ _ hab] at hm
  have hx := wuImprovementLimit_upper_cross hδ (by linarith : δ ≤ 1/10)
    (by linarith : 2 ≤ s) ht (by norm_num : (9/2 : ℝ) ≤ 10)
  have hn := wuImprovementLimit_nonneg true hδ (by linarith : δ < 1/2)
    (by norm_num : (1 : ℝ) ≤ 9/2) (by norm_num : (9/2 : ℝ) ≤ 10)
  norm_num at hx
  nlinarith only [hm,hx,hn]

/-- The second full cross has the original quadratic H profile throughout its support. -/
theorem h_full_cross {δ s : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hs : 4 ≤ s) (ht : s ≤ 11/2) :
    (11/2-s)^3/70875 ≤ wuImprovementLimit false δ s := by
  have hab : s-1 ≤ 9/2 := by linarith
  have hi := wuImprovementLimit_div_intervalIntegrable true hδ
    (by linarith : δ < 1/2) (by linarith : 1 ≤ s-1) hab (by norm_num : (9/2 : ℝ) ≤ 10)
  have hm : (∫ u in (s-1)..(9/2 : ℝ), (9/2-u)^2/(47250/2)) ≤
      ∫ u in (s-1)..(9/2 : ℝ), wuImprovementLimit true δ u/u := by
    apply intervalIntegral.integral_mono_on hab
      ((((continuous_const.sub continuous_id).pow 2).div_const (47250/2)).intervalIntegrable _ _) hi
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hl := H_full_cross hδ hd (by linarith [hu.1] : 3 ≤ u) hu.2
    have hh := mul_nonneg (sq_nonneg (9/2-u)) (show 0 ≤ 9/2-u by linarith [hu.2])
    apply (le_div_iff₀ hu0).mpr
    dsimp only [Pi.sub_apply, Pi.pow_apply, id_eq] at *
    nlinarith only [hl,hh]
  rw [intervalIntegral.integral_div, quadratic_tail] at hm
  have hx := wuImprovementLimit_lower_cross hδ (by linarith : δ ≤ 1/10)
    (by linarith : 2 ≤ s) ht (by norm_num : (11/2 : ℝ) ≤ 10)
  have hn := wuImprovementLimit_nonneg false hδ (by linarith : δ < 1/2)
    (by norm_num : (1 : ℝ) ≤ 11/2) (by norm_num : (11/2 : ℝ) ≤ 10)
  norm_num at hx
  nlinarith only [hm,hx,hn]

end
end PositiveCoreResume
