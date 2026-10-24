import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints420
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_420 (j : Fin 16) (hj : 16*420+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*420+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*420+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6720) ≤ val WuPaper.ClassicalFourthData.Bq 6720
    have hp : val WuPaper.ClassicalFourthData.Bq 6720 = (267884998511655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6720 = 267884998511655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6720 = (92:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6720
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6721) ≤ val WuPaper.ClassicalFourthData.Bq 6721
    have hp : val WuPaper.ClassicalFourthData.Bq 6721 = (267892146934132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6721 = 267892146934132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6721 = (14721:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6721
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6722) ≤ val WuPaper.ClassicalFourthData.Bq 6722
    have hp : val WuPaper.ClassicalFourthData.Bq 6722 = (267899292021623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6722 = 267899292021623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6722 = (7361:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6722
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6723) ≤ val WuPaper.ClassicalFourthData.Bq 6723
    have hp : val WuPaper.ClassicalFourthData.Bq 6723 = (267906433775248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6723 = 267906433775248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6723 = (14723:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6723
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6724) ≤ val WuPaper.ClassicalFourthData.Bq 6724
    have hp : val WuPaper.ClassicalFourthData.Bq 6724 = (267913572196129:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6724 = 267913572196129 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6724 = (3681:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6724
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6725) ≤ val WuPaper.ClassicalFourthData.Bq 6725
    have hp : val WuPaper.ClassicalFourthData.Bq 6725 = (267920707285384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6725 = 267920707285384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6725 = (589:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6725
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6726) ≤ val WuPaper.ClassicalFourthData.Bq 6726
    have hp : val WuPaper.ClassicalFourthData.Bq 6726 = (267927839044132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6726 = 267927839044132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6726 = (7363:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6726
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6727) ≤ val WuPaper.ClassicalFourthData.Bq 6727
    have hp : val WuPaper.ClassicalFourthData.Bq 6727 = (267934967473492:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6727 = 267934967473492 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6727 = (14727:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6727
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6728) ≤ val WuPaper.ClassicalFourthData.Bq 6728
    have hp : val WuPaper.ClassicalFourthData.Bq 6728 = (267942092574583:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6728 = 267942092574583 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6728 = (1841:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6728
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6729) ≤ val WuPaper.ClassicalFourthData.Bq 6729
    have hp : val WuPaper.ClassicalFourthData.Bq 6729 = (267949214348523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6729 = 267949214348523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6729 = (14729:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6729
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6730) ≤ val WuPaper.ClassicalFourthData.Bq 6730
    have hp : val WuPaper.ClassicalFourthData.Bq 6730 = (267956332796428:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6730 = 267956332796428 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6730 = (1473:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6730
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6731) ≤ val WuPaper.ClassicalFourthData.Bq 6731
    have hp : val WuPaper.ClassicalFourthData.Bq 6731 = (267963447919416:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6731 = 267963447919416 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6731 = (14731:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6731
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6732) ≤ val WuPaper.ClassicalFourthData.Bq 6732
    have hp : val WuPaper.ClassicalFourthData.Bq 6732 = (267970559718604:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6732 = 267970559718604 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6732 = (3683:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6732
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6733) ≤ val WuPaper.ClassicalFourthData.Bq 6733
    have hp : val WuPaper.ClassicalFourthData.Bq 6733 = (267977668195107:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6733 = 267977668195107 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6733 = (14733:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6733
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6734) ≤ val WuPaper.ClassicalFourthData.Bq 6734
    have hp : val WuPaper.ClassicalFourthData.Bq 6734 = (267984773350042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6734 = 267984773350042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6734 = (7367:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6734
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6735) ≤ val WuPaper.ClassicalFourthData.Bq 6735
    have hp : val WuPaper.ClassicalFourthData.Bq 6735 = (267991875184523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6735 = 267991875184523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6735 = (2947:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6735
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_420
