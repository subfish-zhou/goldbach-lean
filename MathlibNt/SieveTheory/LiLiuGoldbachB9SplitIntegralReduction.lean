import MathlibNt.SieveTheory.LiLiuGoldbachB9InnerIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachB9LogGridLimit

open MeasureTheory Set
open scoped Interval
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- Exact inner integral with the additional low-first-prime factor from Eq. (5.45).
This is a scalar identity, not an estimate for the actual low counting function. -/
theorem goldbachB9InnerWeightedIntegral_eq {u : ℝ}
    (hu : u ∈ Icc (4 / 53 : ℝ) (1 / 3)) :
    (∫ v in (1 / 3 : ℝ)..((1 - u) / 2),
      1 / (u * v * (1 - u - v) * (1 - u))) =
      Real.log (2 - 3 * u) / (u * (1 - u)^2) := by
  have heq (v : ℝ) : 1 / (u * v * (1 - u - v) * (1 - u)) =
      (1 / (u * v * (1 - u - v))) * (1 / (1 - u)) := by
    simp only [one_div, mul_inv]
  simp_rw [heq]
  rw [intervalIntegral.integral_mul_const, goldbachB9InnerIntegral_eq_logTwoSubThree hu]
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have hu1 : 1 - u ≠ 0 := by linarith [hu.2]
  field_simp [hu0, hu1]

theorem goldbachB9SubintervalIntegral_eq_single {a b : ℝ}
    (ha : (4 / 53 : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (1 / 3 : ℝ)) :
    (∫ u in a..b, ∫ v in (1 / 3 : ℝ)..((1 - u) / 2),
      1 / (u * v * (1 - u - v))) =
      ∫ u in a..b, Real.log (2 - 3 * u) / (u * (1 - u)) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hab] at hu
  exact goldbachB9InnerIntegral_eq_logTwoSubThree ⟨ha.trans hu.1, hu.2.trans hb⟩

theorem goldbachB9WeightedSubintervalIntegral_eq_single {a b : ℝ}
    (ha : (4 / 53 : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (1 / 3 : ℝ)) :
    (∫ u in a..b, ∫ v in (1 / 3 : ℝ)..((1 - u) / 2),
      1 / (u * v * (1 - u - v) * (1 - u))) =
      ∫ u in a..b, Real.log (2 - 3 * u) / (u * (1 - u)^2) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hab] at hu
  exact goldbachB9InnerWeightedIntegral_eq ⟨ha.trans hu.1, hu.2.trans hb⟩

/-- The literal scalar expression in the paper, without any assertion that it bounds S5. -/
def goldbachB9PaperSplitIntegral : ℝ :=
  (36 / 5 : ℝ) * (∫ u in (4 / 53 : ℝ)..(1 / 10),
    ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v) * (1 - u))) +
  8 * (∫ u in (1 / 10 : ℝ)..(1 / 3),
    ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v)))

theorem goldbachB9PaperSplitIntegral_eq_singleIntegrals :
    goldbachB9PaperSplitIntegral =
      (36 / 5 : ℝ) * (∫ u in (4 / 53 : ℝ)..(1 / 10),
        Real.log (2 - 3 * u) / (u * (1 - u)^2)) +
      8 * (∫ u in (1 / 10 : ℝ)..(1 / 3),
        Real.log (2 - 3 * u) / (u * (1 - u))) := by
  unfold goldbachB9PaperSplitIntegral
  rw [goldbachB9WeightedSubintervalIntegral_eq_single le_rfl (by norm_num) (by norm_num),
    goldbachB9SubintervalIntegral_eq_single (by norm_num) (by norm_num) le_rfl]

theorem continuousOn_goldbachB9WeightedSingleIntegrand :
    ContinuousOn (fun u : ℝ => Real.log (2 - 3 * u) / (u * (1 - u)^2))
      (Icc (4 / 53 : ℝ) (1 / 3)) := by
  apply ContinuousOn.div
    ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).log
      (fun u hu => by change 2 - 3 * u ≠ 0; linarith [hu.2]))
    (continuousOn_id.mul ((continuousOn_const.sub continuousOn_id).pow 2))
  intro u hu
  change u * (1 - u)^2 ≠ 0
  exact mul_ne_zero (by linarith [hu.1]) (pow_ne_zero 2 (by linarith [hu.2]))

theorem intervalIntegrable_goldbachB9WeightedSingleIntegrand :
    IntervalIntegrable (fun u : ℝ => Real.log (2 - 3 * u) / (u * (1 - u)^2))
      volume (4 / 53) (1 / 3) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 1 / 3)]
  exact continuousOn_goldbachB9WeightedSingleIntegrand

theorem intervalIntegrable_goldbachB9WeightedInner {u : ℝ}
    (hu : u ∈ Icc (4 / 53 : ℝ) (1 / 3)) :
    IntervalIntegrable (fun v : ℝ => 1 / (u * v * (1 - u - v) * (1 - u)))
      volume (1 / 3) ((1 - u) / 2) := by
  simpa only [one_div, mul_inv] using
    (intervalIntegrable_goldbachB9MainInner hu).mul_const (1 / (1 - u))

theorem intervalIntegrable_goldbachB9WeightedOuter :
    IntervalIntegrable (fun u : ℝ => ∫ v in (1 / 3 : ℝ)..((1 - u) / 2),
      1 / (u * v * (1 - u - v) * (1 - u))) volume (4 / 53) (1 / 3) := by
  apply intervalIntegrable_goldbachB9WeightedSingleIntegrand.congr
  intro u hu
  rw [uIoc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 1 / 3)] at hu
  exact (goldbachB9InnerWeightedIntegral_eq ⟨hu.1.le, hu.2⟩).symm

/-- Continuous interval splitting is justified by integrability; it does not alter
how the finite first-prime boundary is assigned to the high counting family. -/
theorem goldbachB9MainIntegral_eq_splitSingleIntegrals :
    goldbachB9MainIntegral =
      (∫ u in (4 / 53 : ℝ)..(1 / 10), Real.log (2 - 3 * u) / (u * (1 - u))) +
      (∫ u in (1 / 10 : ℝ)..(1 / 3), Real.log (2 - 3 * u) / (u * (1 - u))) := by
  have hl : IntervalIntegrable (fun u : ℝ => Real.log (2 - 3 * u) / (u * (1 - u)))
      volume (4 / 53) (1 / 10) := by
    apply intervalIntegrable_goldbachB9SingleIntegrand.mono_set
    rw [uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 1 / 10),
      uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 1 / 3)]
    exact Icc_subset_Icc_right (by norm_num)
  have hr : IntervalIntegrable (fun u : ℝ => Real.log (2 - 3 * u) / (u * (1 - u)))
      volume (1 / 10) (1 / 3) := by
    apply intervalIntegrable_goldbachB9SingleIntegrand.mono_set
    rw [uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3),
      uIcc_of_le (by norm_num : (4 / 53 : ℝ) ≤ 1 / 3)]
    exact Icc_subset_Icc_left (by norm_num)
  unfold goldbachB9MainIntegral
  rw [goldbachB9DoubleIntegral_eq_singleIntegral]
  exact (intervalIntegral.integral_add_adjacent_intervals hl hr).symm

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig