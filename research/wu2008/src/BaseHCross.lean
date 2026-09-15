import BaseHRaw

namespace Wu2008DoubleSieve.BaseHGain
open Set MeasureTheory
open scoped Interval

/-- First extra cross step, integrating only inside the established lower seed. -/
theorem H_extended {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000)
    (hs : 3 ≤ s) (hsHi : s ≤ 9/2) :
    (9/2-s)^2/10500 ≤ wuImprovementLimit true δ s := by
  let t : ℝ := (s+9/2)/2
  have hst : s ≤ t := by dsimp [t]; linarith
  have ht : t ≤ 9/2 := by dsimp [t]; linarith
  have hab : s-1 ≤ t-1 := by linarith
  have hi := wuImprovementLimit_div_intervalIntegrable false hδ
    (by linarith : δ < 1/2) (by linarith : 1 ≤ s-1) hab
    (by linarith : t-1 ≤ 10)
  have hm : (∫ u in (s-1)..(t-1), (9/2-s)/5250) ≤
      ∫ u in (s-1)..(t-1), wuImprovementLimit false δ u/u := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const hi
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hl : (7/2-u)/750 ≤ wuImprovementLimit false δ u := by
      by_cases he : u < 7/2
      · exact (SecondFunctionalSmallDelta.h_strict hδ hδhi (by linarith [hu.1]) he).le
      · have heq : u = 7/2 := by linarith [hu.2]
        rw [heq]
        norm_num only [sub_self, zero_div]
        exact wuImprovementLimit_nonneg false hδ (by linarith) (by norm_num) (by norm_num)
    apply (le_div_iff₀ hu0).mpr
    have hd : 0 ≤ 9/2-s := by linarith
    have hub : u ≤ 7/2 := by linarith [hu.2]
    have hm := mul_le_mul_of_nonneg_left hub hd
    have hmid : u ≤ (s+9/2)/2-1 := hu.2
    nlinarith only [hl, hm, hmid]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  have hx := wuImprovementLimit_upper_cross hδ (by linarith : δ ≤ 1/10) (by linarith : 2 ≤ s) hst (by linarith : t ≤ 10)
  have hn := wuImprovementLimit_nonneg true hδ (by linarith : δ < 1/2)
    (by linarith : 1 ≤ t) (by linarith : t ≤ 10)
  dsimp [t] at hm
  nlinarith

/-- Second extra cross step; no seed is evaluated beyond its proved interval. -/
theorem h_extended {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000)
    (hs : 4 ≤ s) (hsHi : s ≤ 11/2) :
    (11/2-s)^3/378000 ≤ wuImprovementLimit false δ s := by
  let t : ℝ := (s+11/2)/2
  have hst : s ≤ t := by dsimp [t]; linarith
  have ht : t ≤ 11/2 := by dsimp [t]; linarith
  have hab : s-1 ≤ t-1 := by linarith
  have hi := wuImprovementLimit_div_intervalIntegrable true hδ
    (by linarith : δ < 1/2) (by linarith : 1 ≤ s-1) hab
    (by linarith : t-1 ≤ 10)
  have hm : (∫ u in (s-1)..(t-1), (11/2-s)^2/189000) ≤
      ∫ u in (s-1)..(t-1), wuImprovementLimit true δ u/u := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const hi
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hl := H_extended hδ hδhi (by linarith [hu.1] : 3 ≤ u)
      (by linarith [hu.2] : u ≤ 9/2)
    have hsq : ((11/2-s)/2)^2 ≤ (9/2-u)^2 := by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [t] at hu
      linarith [hu.2]
    have hm := mul_le_mul_of_nonneg_left (show u ≤ 9/2 by linarith [hu.2])
      (sq_nonneg (11/2-s))
    apply (le_div_iff₀ hu0).mpr
    nlinarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  have hx := wuImprovementLimit_lower_cross hδ (by linarith : δ ≤ 1/10) (by linarith : 2 ≤ s) hst (by linarith : t ≤ 10)
  have hn := wuImprovementLimit_nonneg false hδ (by linarith : δ < 1/2)
    (by linarith : 1 ≤ t) (by linarith : t ≤ 10)
  have he : (t-1-(s-1))*((11/2-s)^2/189000) = (11/2-s)^3/378000 := by
    dsimp [t]
    ring
  rw [he] at hm
  linarith

/-- Uniform strictly positive lower improvement at the unchanged original F2 exponent. -/
theorem original_F2_h {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) :
    (11/2-(1/(2*(25/206))))^3/378000 ≤
      wuImprovementLimit false δ ((1/2-δ)/(25/206)) := by
  have hs : (4 : ℝ) ≤ (1/2-δ)/(25/206) := by norm_num; linarith
  have ht : (1/2-δ)/(25/206) ≤ (11/2 : ℝ) := by norm_num; linarith
  have hl := h_extended hδ hδhi hs ht
  have hp : (11/2-(1/(2*(25/206 : ℝ))))^3 ≤
      (11/2-(1/2-δ)/(25/206))^3 := by
    apply pow_le_pow_left₀ (by norm_num)
    norm_num
    linarith
  exact (div_le_div_of_nonneg_right hp (by norm_num)).trans hl

end Wu2008DoubleSieve.BaseHGain
