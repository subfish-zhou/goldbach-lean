import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints359
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_359 (j : Fin 16) (hj : 16*359+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*359+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*359+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5744) ≤ val WuPaper.ClassicalFourthData.Bq 5744
    have hp : val WuPaper.ClassicalFourthData.Bq 5744 = (259126120444604:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5744 = 259126120444604 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5744 = (859:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5744
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5745) ≤ val WuPaper.ClassicalFourthData.Bq 5745
    have hp : val WuPaper.ClassicalFourthData.Bq 5745 = (259137132583381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5745 = 259137132583381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5745 = (2749:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5745
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5746) ≤ val WuPaper.ClassicalFourthData.Bq 5746
    have hp : val WuPaper.ClassicalFourthData.Bq 5746 = (259148140055706:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5746 = 259148140055706 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5746 = (6873:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5746
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5747) ≤ val WuPaper.ClassicalFourthData.Bq 5747
    have hp : val WuPaper.ClassicalFourthData.Bq 5747 = (259159142863226:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5747 = 259159142863226 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5747 = (13747:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5747
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5748) ≤ val WuPaper.ClassicalFourthData.Bq 5748
    have hp : val WuPaper.ClassicalFourthData.Bq 5748 = (259170141007588:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5748 = 259170141007588 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5748 = (3437:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5748
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5749) ≤ val WuPaper.ClassicalFourthData.Bq 5749
    have hp : val WuPaper.ClassicalFourthData.Bq 5749 = (259181134490437:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5749 = 259181134490437 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5749 = (13749:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5749
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5750) ≤ val WuPaper.ClassicalFourthData.Bq 5750
    have hp : val WuPaper.ClassicalFourthData.Bq 5750 = (259192123313418:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5750 = 259192123313418 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5750 = (55:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5750
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5751) ≤ val WuPaper.ClassicalFourthData.Bq 5751
    have hp : val WuPaper.ClassicalFourthData.Bq 5751 = (259203107478176:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5751 = 259203107478176 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5751 = (13751:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5751
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5752) ≤ val WuPaper.ClassicalFourthData.Bq 5752
    have hp : val WuPaper.ClassicalFourthData.Bq 5752 = (259214086986355:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5752 = 259214086986355 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5752 = (1719:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5752
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5753) ≤ val WuPaper.ClassicalFourthData.Bq 5753
    have hp : val WuPaper.ClassicalFourthData.Bq 5753 = (259225061839598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5753 = 259225061839598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5753 = (13753:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5753
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5754) ≤ val WuPaper.ClassicalFourthData.Bq 5754
    have hp : val WuPaper.ClassicalFourthData.Bq 5754 = (259236032039546:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5754 = 259236032039546 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5754 = (6877:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5754
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5755) ≤ val WuPaper.ClassicalFourthData.Bq 5755
    have hp : val WuPaper.ClassicalFourthData.Bq 5755 = (259246997587842:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5755 = 259246997587842 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5755 = (2751:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5755
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5756) ≤ val WuPaper.ClassicalFourthData.Bq 5756
    have hp : val WuPaper.ClassicalFourthData.Bq 5756 = (259257958486128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5756 = 259257958486128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5756 = (3439:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5756
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5757) ≤ val WuPaper.ClassicalFourthData.Bq 5757
    have hp : val WuPaper.ClassicalFourthData.Bq 5757 = (259268914736042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5757 = 259268914736042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5757 = (13757:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5757
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5758) ≤ val WuPaper.ClassicalFourthData.Bq 5758
    have hp : val WuPaper.ClassicalFourthData.Bq 5758 = (259279866339225:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5758 = 259279866339225 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5758 = (6879:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5758
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5759) ≤ val WuPaper.ClassicalFourthData.Bq 5759
    have hp : val WuPaper.ClassicalFourthData.Bq 5759 = (259290813297316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5759 = 259290813297316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5759 = (13759:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5759
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_359
