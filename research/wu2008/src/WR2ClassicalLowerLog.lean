import WR2ClassicalCWeighted
import WE07FifthSourceCover
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthZeroDeltaClassical

noncomputable section
namespace WuPaper.ClassicalLowerLog
open Real Set Wu2008DoubleSieve Wu08OriginalFirstSteps

/-- The logarithmic lower coefficient, continuously extended through its zero range. -/
def profile (s : ℝ) : ℝ := log (max 1 (s-1))

theorem profile_continuous : Continuous profile := by
  unfold profile
  apply Continuous.log (by fun_prop)
  intro s
  exact (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)).ne'

theorem profile_zero {s : ℝ} (hs : s ≤ 2) : profile s = 0 := by
  simp [profile,max_eq_left (show s-1 ≤ (1:ℝ) by linarith)]

theorem profile_literal {s : ℝ} (hs : 2 ≤ s) : profile s = log (s-1) := by
  rw [profile,max_eq_right (show (1:ℝ) ≤ s-1 by linarith)]

/-- Dropping the positive recurrence correction is a proved lower bound, including both boundaries. -/
theorem profile_le_lower {s : ℝ} (hs6 : s ≤ 6) : profile s ≤ wuLowerCoefficient s := by
  by_cases h2 : s ≤ 2
  · rw [profile_zero h2,truncatedSixthZeroDelta_coefficient_zero h2]
  · have hs2 : 2 ≤ s := (lt_of_not_ge h2).le
    rw [profile_literal hs2]
    by_cases h4 : s ≤ 4
    · rw [WuTarget.Wu08FifthSource.coefficient_initial hs2 h4]
    · rw [lower_middle (by linarith) hs6]
      have hc := (ClassicalCWeighted.C_bounds (by linarith) hs6).1
      linarith only [hc]

theorem profile_bounds {s : ℝ} (hs5 : s ≤ 5) : 0 ≤ profile s ∧ profile s ≤ 3 := by
  have hp : 0 < max (1:ℝ) (s-1) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hm : max (1:ℝ) (s-1) ≤ 4 := max_le (by norm_num) (by linarith)
  exact ⟨log_nonneg (le_max_left _ _),(log_le_sub_one_of_pos hp).trans (by linarith only [hm])⟩

end WuPaper.ClassicalLowerLog
#print axioms WuPaper.ClassicalLowerLog.profile_le_lower
#print axioms WuPaper.ClassicalLowerLog.profile_bounds
