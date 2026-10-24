import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints610
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_610 (j : Fin 16) (hj : 16*610+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*610+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*610+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9760) ≤ val WuPaper.ClassicalFourthData.Bq 9760
    have hp : val WuPaper.ClassicalFourthData.Bq 9760 = (278259340416753:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9760 = 278259340416753 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9760 = (111:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9760
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9761) ≤ val WuPaper.ClassicalFourthData.Bq 9761
    have hp : val WuPaper.ClassicalFourthData.Bq 9761 = (278260040139280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9761 = 278260040139280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9761 = (17761:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9761
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9762) ≤ val WuPaper.ClassicalFourthData.Bq 9762
    have hp : val WuPaper.ClassicalFourthData.Bq 9762 = (278260738593781:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9762 = 278260738593781 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9762 = (8881:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9762
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9763) ≤ val WuPaper.ClassicalFourthData.Bq 9763
    have hp : val WuPaper.ClassicalFourthData.Bq 9763 = (278261435780645:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9763 = 278261435780645 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9763 = (17763:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9763
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9764) ≤ val WuPaper.ClassicalFourthData.Bq 9764
    have hp : val WuPaper.ClassicalFourthData.Bq 9764 = (278262131700257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9764 = 278262131700257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9764 = (4441:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9764
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9765) ≤ val WuPaper.ClassicalFourthData.Bq 9765
    have hp : val WuPaper.ClassicalFourthData.Bq 9765 = (278262826353005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9765 = 278262826353005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9765 = (3553:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9765
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9766) ≤ val WuPaper.ClassicalFourthData.Bq 9766
    have hp : val WuPaper.ClassicalFourthData.Bq 9766 = (278263519739275:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9766 = 278263519739275 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9766 = (8883:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9766
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9767) ≤ val WuPaper.ClassicalFourthData.Bq 9767
    have hp : val WuPaper.ClassicalFourthData.Bq 9767 = (278264211859454:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9767 = 278264211859454 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9767 = (17767:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9767
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9768) ≤ val WuPaper.ClassicalFourthData.Bq 9768
    have hp : val WuPaper.ClassicalFourthData.Bq 9768 = (278264902713928:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9768 = 278264902713928 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9768 = (2221:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9768
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9769) ≤ val WuPaper.ClassicalFourthData.Bq 9769
    have hp : val WuPaper.ClassicalFourthData.Bq 9769 = (278265592303084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9769 = 278265592303084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9769 = (17769:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9769
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9770) ≤ val WuPaper.ClassicalFourthData.Bq 9770
    have hp : val WuPaper.ClassicalFourthData.Bq 9770 = (278266280627306:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9770 = 278266280627306 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9770 = (1777:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9770
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9771) ≤ val WuPaper.ClassicalFourthData.Bq 9771
    have hp : val WuPaper.ClassicalFourthData.Bq 9771 = (278266967686982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9771 = 278266967686982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9771 = (17771:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9771
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9772) ≤ val WuPaper.ClassicalFourthData.Bq 9772
    have hp : val WuPaper.ClassicalFourthData.Bq 9772 = (278267653482497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9772 = 278267653482497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9772 = (4443:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9772
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9773) ≤ val WuPaper.ClassicalFourthData.Bq 9773
    have hp : val WuPaper.ClassicalFourthData.Bq 9773 = (278268338014237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9773 = 278268338014237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9773 = (17773:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9773
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9774) ≤ val WuPaper.ClassicalFourthData.Bq 9774
    have hp : val WuPaper.ClassicalFourthData.Bq 9774 = (278269021282588:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9774 = 278269021282588 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9774 = (8887:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9774
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9775) ≤ val WuPaper.ClassicalFourthData.Bq 9775
    have hp : val WuPaper.ClassicalFourthData.Bq 9775 = (278269703287934:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9775 = 278269703287934 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9775 = (711:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9775
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_610
