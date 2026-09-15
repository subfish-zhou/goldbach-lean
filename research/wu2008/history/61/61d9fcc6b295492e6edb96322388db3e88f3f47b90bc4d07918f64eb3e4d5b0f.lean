import MathlibNt.Wu2008DoubleSieve.ImprovementIntegrals

/-!
# The actual normalized Wu coefficient recurrences

Wu (2004), after (3.20), prints a recurrence without the denominator.
The frozen Jurkat--Richert recurrences give both identities below with the
required `/ t`. They hold already for every `2 ≤ s ≤ s'`, including `s = 2`;
thus the shifted interval starts at `1`, never at the singular point `0`.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem wuUpperCoefficient_div {t : ℝ} (ht : t ≠ 0) :
    wuUpperCoefficient t / t =
      jr1965F t / (2 * exp eulerMascheroniConstant) := by
  unfold wuUpperCoefficient
  field_simp

theorem wuLowerCoefficient_div {t : ℝ} (ht : t ≠ 0) :
    wuLowerCoefficient t / t =
      jr1965f t / (2 * exp eulerMascheroniConstant) := by
  unfold wuLowerCoefficient
  field_simp

/-- The genuine lower coefficient identity, including the left endpoint two. -/
theorem wuLowerCoefficient_sub_eq_integral {s s' : ℝ}
    (hs : 2 ≤ s) (hss' : s ≤ s') :
    wuLowerCoefficient s' - wuLowerCoefficient s =
      ∫ t in (s - 1)..(s' - 1), wuUpperCoefficient t / t := by
  have hrec := jr1965f_integral_recurrence hs hss'
  rw [intervalIntegral.integral_comp_sub_right] at hrec
  calc
    _ = (∫ t in (s - 1)..(s' - 1), jr1965F t) /
        (2 * exp eulerMascheroniConstant) := by
      unfold wuLowerCoefficient
      rw [hrec]
      ring
    _ = ∫ t in (s - 1)..(s' - 1),
        jr1965F t / (2 * exp eulerMascheroniConstant) := by
      rw [intervalIntegral.integral_div]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith : s - 1 ≤ s' - 1)] at ht
      exact (wuUpperCoefficient_div (by linarith [ht.1])).symm

/-- The genuine upper coefficient identity; no exclusion of `s = 2` is needed. -/
theorem wuUpperCoefficient_sub_eq_integral {s s' : ℝ}
    (hs : 2 ≤ s) (hss' : s ≤ s') :
    wuUpperCoefficient s' - wuUpperCoefficient s =
      ∫ t in (s - 1)..(s' - 1), wuLowerCoefficient t / t := by
  have hrec := jr1965F_integral_recurrence hs hss'
  rw [intervalIntegral.integral_comp_sub_right] at hrec
  calc
    _ = (∫ t in (s - 1)..(s' - 1), jr1965f t) /
        (2 * exp eulerMascheroniConstant) := by
      unfold wuUpperCoefficient
      rw [hrec]
      ring
    _ = ∫ t in (s - 1)..(s' - 1),
        jr1965f t / (2 * exp eulerMascheroniConstant) := by
      rw [intervalIntegral.integral_div]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith : s - 1 ≤ s' - 1)] at ht
      exact (wuLowerCoefficient_div (by linarith [ht.1])).symm

theorem wuUpperCoefficient_div_intervalIntegrable {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => wuUpperCoefficient t / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_wuUpperCoefficient.mono ?_).div continuousOn_id ?_
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact (ha.trans_le ht.1).ne'

theorem wuLowerCoefficient_div_intervalIntegrable {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => wuLowerCoefficient t / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_wuLowerCoefficient.mono ?_).div continuousOn_id ?_
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact (ha.trans_le ht.1).ne'

end Wu2008DoubleSieve
