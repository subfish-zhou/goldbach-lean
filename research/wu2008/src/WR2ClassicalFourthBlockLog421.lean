import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints421
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_421 (j : Fin 16) (hj : 16*421+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*421+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*421+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6736) ≤ val WuPaper.ClassicalFourthData.Bq 6736
    have hp : val WuPaper.ClassicalFourthData.Bq 6736 = (267998973699665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6736 = 267998973699665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6736 = (921:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6736
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6737) ≤ val WuPaper.ClassicalFourthData.Bq 6737
    have hp : val WuPaper.ClassicalFourthData.Bq 6737 = (268006068896584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6737 = 268006068896584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6737 = (14737:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6737
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6738) ≤ val WuPaper.ClassicalFourthData.Bq 6738
    have hp : val WuPaper.ClassicalFourthData.Bq 6738 = (268013160776393:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6738 = 268013160776393 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6738 = (7369:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6738
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6739) ≤ val WuPaper.ClassicalFourthData.Bq 6739
    have hp : val WuPaper.ClassicalFourthData.Bq 6739 = (268020249340205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6739 = 268020249340205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6739 = (14739:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6739
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6740) ≤ val WuPaper.ClassicalFourthData.Bq 6740
    have hp : val WuPaper.ClassicalFourthData.Bq 6740 = (268027334589135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6740 = 268027334589135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6740 = (737:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6740
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6741) ≤ val WuPaper.ClassicalFourthData.Bq 6741
    have hp : val WuPaper.ClassicalFourthData.Bq 6741 = (268034416524294:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6741 = 268034416524294 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6741 = (14741:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6741
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6742) ≤ val WuPaper.ClassicalFourthData.Bq 6742
    have hp : val WuPaper.ClassicalFourthData.Bq 6742 = (268041495146795:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6742 = 268041495146795 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6742 = (7371:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6742
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6743) ≤ val WuPaper.ClassicalFourthData.Bq 6743
    have hp : val WuPaper.ClassicalFourthData.Bq 6743 = (268048570457749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6743 = 268048570457749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6743 = (14743:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6743
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6744) ≤ val WuPaper.ClassicalFourthData.Bq 6744
    have hp : val WuPaper.ClassicalFourthData.Bq 6744 = (268055642458269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6744 = 268055642458269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6744 = (1843:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6744
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6745) ≤ val WuPaper.ClassicalFourthData.Bq 6745
    have hp : val WuPaper.ClassicalFourthData.Bq 6745 = (268062711149466:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6745 = 268062711149466 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6745 = (2949:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6745
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6746) ≤ val WuPaper.ClassicalFourthData.Bq 6746
    have hp : val WuPaper.ClassicalFourthData.Bq 6746 = (268069776532449:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6746 = 268069776532449 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6746 = (7373:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6746
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6747) ≤ val WuPaper.ClassicalFourthData.Bq 6747
    have hp : val WuPaper.ClassicalFourthData.Bq 6747 = (268076838608330:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6747 = 268076838608330 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6747 = (14747:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6747
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6748) ≤ val WuPaper.ClassicalFourthData.Bq 6748
    have hp : val WuPaper.ClassicalFourthData.Bq 6748 = (268083897378218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6748 = 268083897378218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6748 = (3687:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6748
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6749) ≤ val WuPaper.ClassicalFourthData.Bq 6749
    have hp : val WuPaper.ClassicalFourthData.Bq 6749 = (268090952843223:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6749 = 268090952843223 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6749 = (14749:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6749
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6750) ≤ val WuPaper.ClassicalFourthData.Bq 6750
    have hp : val WuPaper.ClassicalFourthData.Bq 6750 = (268098005004452:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6750 = 268098005004452 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6750 = (59:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6750
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6751) ≤ val WuPaper.ClassicalFourthData.Bq 6751
    have hp : val WuPaper.ClassicalFourthData.Bq 6751 = (268105053863016:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6751 = 268105053863016 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6751 = (14751:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6751
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_421
