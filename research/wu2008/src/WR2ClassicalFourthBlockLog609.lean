import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints609
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_609 (j : Fin 16) (hj : 16*609+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*609+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*609+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9744) ≤ val WuPaper.ClassicalFourthData.Bq 9744
    have hp : val WuPaper.ClassicalFourthData.Bq 9744 = (278247972088690:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9744 = 278247972088690 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9744 = (1109:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9744
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9745) ≤ val WuPaper.ClassicalFourthData.Bq 9745
    have hp : val WuPaper.ClassicalFourthData.Bq 9745 = (278248692152345:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9745 = 278248692152345 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9745 = (3549:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9745
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9746) ≤ val WuPaper.ClassicalFourthData.Bq 9746
    have hp : val WuPaper.ClassicalFourthData.Bq 9746 = (278249410941766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9746 = 278249410941766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9746 = (8873:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9746
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9747) ≤ val WuPaper.ClassicalFourthData.Bq 9747
    have hp : val WuPaper.ClassicalFourthData.Bq 9747 = (278250128457344:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9747 = 278250128457344 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9747 = (17747:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9747
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9748) ≤ val WuPaper.ClassicalFourthData.Bq 9748
    have hp : val WuPaper.ClassicalFourthData.Bq 9748 = (278250844699465:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9748 = 278250844699465 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9748 = (4437:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9748
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9749) ≤ val WuPaper.ClassicalFourthData.Bq 9749
    have hp : val WuPaper.ClassicalFourthData.Bq 9749 = (278251559668520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9749 = 278251559668520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9749 = (17749:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9749
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9750) ≤ val WuPaper.ClassicalFourthData.Bq 9750
    have hp : val WuPaper.ClassicalFourthData.Bq 9750 = (278252273364896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9750 = 278252273364896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9750 = (71:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9750
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9751) ≤ val WuPaper.ClassicalFourthData.Bq 9751
    have hp : val WuPaper.ClassicalFourthData.Bq 9751 = (278252985788982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9751 = 278252985788982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9751 = (17751:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9751
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9752) ≤ val WuPaper.ClassicalFourthData.Bq 9752
    have hp : val WuPaper.ClassicalFourthData.Bq 9752 = (278253696941167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9752 = 278253696941167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9752 = (2219:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9752
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9753) ≤ val WuPaper.ClassicalFourthData.Bq 9753
    have hp : val WuPaper.ClassicalFourthData.Bq 9753 = (278254406821839:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9753 = 278254406821839 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9753 = (17753:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9753
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9754) ≤ val WuPaper.ClassicalFourthData.Bq 9754
    have hp : val WuPaper.ClassicalFourthData.Bq 9754 = (278255115431386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9754 = 278255115431386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9754 = (8877:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9754
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9755) ≤ val WuPaper.ClassicalFourthData.Bq 9755
    have hp : val WuPaper.ClassicalFourthData.Bq 9755 = (278255822770195:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9755 = 278255822770195 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9755 = (3551:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9755
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9756) ≤ val WuPaper.ClassicalFourthData.Bq 9756
    have hp : val WuPaper.ClassicalFourthData.Bq 9756 = (278256528838655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9756 = 278256528838655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9756 = (4439:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9756
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9757) ≤ val WuPaper.ClassicalFourthData.Bq 9757
    have hp : val WuPaper.ClassicalFourthData.Bq 9757 = (278257233637153:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9757 = 278257233637153 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9757 = (17757:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9757
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9758) ≤ val WuPaper.ClassicalFourthData.Bq 9758
    have hp : val WuPaper.ClassicalFourthData.Bq 9758 = (278257937166077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9758 = 278257937166077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9758 = (8879:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9758
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9759) ≤ val WuPaper.ClassicalFourthData.Bq 9759
    have hp : val WuPaper.ClassicalFourthData.Bq 9759 = (278258639425815:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9759 = 278258639425815 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9759 = (17759:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9759
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_609
