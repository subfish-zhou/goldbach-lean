import WR2ClassicalELower
import WR2ClassicalLogSplit
import Wu08TerminalAlignment

noncomputable section
namespace WuPaper.ClassicalFirst
open Real Wu08OriginalFirstSteps Wu08TerminalAlignment

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem first_log_lower : (17289971:ℝ)/10000000 ≤ log (1127/200) := by
  apply le_trans _ (ClassicalLogSplit.bounds 2 (by norm_num : (1:ℝ) ≤ 1127/200)).2.1
  norm_num [ClassicalLogSplit.lower,WuSource.SrcFourEnclosure.logLo,Finset.sum_range_succ]

/-- The positive fourth recurrence term supplies the required first-slot margin. -/
theorem first_lower_of_C (hc : (1336108:ℝ)/10000000 ≤ C (1327/200)) :
    (1490088:ℝ)/100000 ≤ firstMain := by
  have he := ClassicalE.E_lower
  have hl := first_log_lower
  unfold firstMain
  linarith only [hc,he,hl]

end WuPaper.ClassicalFirst
#print axioms WuPaper.ClassicalFirst.first_log_lower
#print axioms WuPaper.ClassicalFirst.first_lower_of_C
