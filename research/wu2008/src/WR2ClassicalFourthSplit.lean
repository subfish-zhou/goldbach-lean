import WR2ClassicalFourthIntegral
import WR2ClassicalFourthKernel

noncomputable section
namespace WuPaper.ClassicalFourth
open Real Set MeasureTheory Wu2008DoubleSieve Wu08OriginalFirstSteps Wu08TerminalAlignment
open scoped Interval

theorem source_integrable {l r : ℝ} (hl : 3 ≤ l) (hr : r ≤ R-1) (hlr : l ≤ r) :
    IntervalIntegrable (fun s => weight s*wuUpperCoefficient s) volume l r := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hlr]
  have hw : ContinuousOn weight (Icc l r) := fun s hs =>
    (weight_deriv (by linarith [hs.1] : s ≠ 0) (by linarith [hs.2] : R-s ≠ 0)).continuousAt.continuousWithinAt
  have ha : ContinuousOn wuUpperCoefficient (Icc l r) :=
    continuousOn_wuUpperCoefficient.mono (fun s hs => by change 0 < s; linarith [hs.1])
  exact hw.mul ha

/-- Splitting at five keeps each numerical cell on one exact recurrence formula. -/
theorem fourth_split : fourthMain =
    4*((∫ s in (3:ℝ)..5, kernel initial s)+(∫ s in (5:ℝ)..(R-1), kernel terminal s)) := by
  have hi1 := source_integrable (by norm_num : (3:ℝ) ≤ 3)
    (by norm_num [R] : (5:ℝ) ≤ R-1) (by norm_num : (3:ℝ) ≤ 5)
  have hi2 := source_integrable (by norm_num : (3:ℝ) ≤ 5)
    (le_refl (R-1)) (by norm_num [R] : (5:ℝ) ≤ R-1)
  have h1 : (∫ s in (3:ℝ)..5, weight s*wuUpperCoefficient s) = ∫ s in (3:ℝ)..5, kernel initial s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (3:ℝ) ≤ 5)] at hs
    dsimp only
    rw [upper_initial hs.1 hs.2]
    rfl
  have h2 : (∫ s in (5:ℝ)..(R-1), weight s*wuUpperCoefficient s) = ∫ s in (5:ℝ)..(R-1), kernel terminal s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num [R] : (5:ℝ) ≤ R-1)] at hs
    dsimp only
    rw [upper_middle hs.1 (by norm_num [R] at hs; linarith [hs.2])]
    rfl
  rw [fourth_integral,← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,h1,h2]

end WuPaper.ClassicalFourth
#print axioms WuPaper.ClassicalFourth.fourth_split
