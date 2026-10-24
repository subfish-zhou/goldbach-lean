import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints540
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_540 (j : Fin 16) (hj : 16*540+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*540+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*540+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8640) ≤ val WuPaper.ClassicalFourthData.Bq 8640
    have hp : val WuPaper.ClassicalFourthData.Bq 8640 = (276579814328844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8640 = 276579814328844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8640 = (104:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8640
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8641) ≤ val WuPaper.ClassicalFourthData.Bq 8641
    have hp : val WuPaper.ClassicalFourthData.Bq 8641 = (276582209819775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8641 = 276582209819775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8641 = (16641:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8641
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8642) ≤ val WuPaper.ClassicalFourthData.Bq 8642
    have hp : val WuPaper.ClassicalFourthData.Bq 8642 = (276584603518669:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8642 = 276584603518669 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8642 = (8321:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8642
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8643) ≤ val WuPaper.ClassicalFourthData.Bq 8643
    have hp : val WuPaper.ClassicalFourthData.Bq 8643 = (276586995426087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8643 = 276586995426087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8643 = (16643:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8643
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8644) ≤ val WuPaper.ClassicalFourthData.Bq 8644
    have hp : val WuPaper.ClassicalFourthData.Bq 8644 = (276589385542591:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8644 = 276589385542591 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8644 = (4161:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8644
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8645) ≤ val WuPaper.ClassicalFourthData.Bq 8645
    have hp : val WuPaper.ClassicalFourthData.Bq 8645 = (276591773868740:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8645 = 276591773868740 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8645 = (3329:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8645
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8646) ≤ val WuPaper.ClassicalFourthData.Bq 8646
    have hp : val WuPaper.ClassicalFourthData.Bq 8646 = (276594160405096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8646 = 276594160405096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8646 = (8323:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8646
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8647) ≤ val WuPaper.ClassicalFourthData.Bq 8647
    have hp : val WuPaper.ClassicalFourthData.Bq 8647 = (276596545152218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8647 = 276596545152218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8647 = (16647:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8647
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8648) ≤ val WuPaper.ClassicalFourthData.Bq 8648
    have hp : val WuPaper.ClassicalFourthData.Bq 8648 = (276598928110666:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8648 = 276598928110666 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8648 = (2081:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8648
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8649) ≤ val WuPaper.ClassicalFourthData.Bq 8649
    have hp : val WuPaper.ClassicalFourthData.Bq 8649 = (276601309281000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8649 = 276601309281000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8649 = (16649:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8649
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8650) ≤ val WuPaper.ClassicalFourthData.Bq 8650
    have hp : val WuPaper.ClassicalFourthData.Bq 8650 = (276603688663780:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8650 = 276603688663780 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8650 = (333:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8650
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8651) ≤ val WuPaper.ClassicalFourthData.Bq 8651
    have hp : val WuPaper.ClassicalFourthData.Bq 8651 = (276606066259565:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8651 = 276606066259565 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8651 = (16651:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8651
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8652) ≤ val WuPaper.ClassicalFourthData.Bq 8652
    have hp : val WuPaper.ClassicalFourthData.Bq 8652 = (276608442068915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8652 = 276608442068915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8652 = (4163:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8652
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8653) ≤ val WuPaper.ClassicalFourthData.Bq 8653
    have hp : val WuPaper.ClassicalFourthData.Bq 8653 = (276610816092388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8653 = 276610816092388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8653 = (16653:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8653
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8654) ≤ val WuPaper.ClassicalFourthData.Bq 8654
    have hp : val WuPaper.ClassicalFourthData.Bq 8654 = (276613188330544:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8654 = 276613188330544 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8654 = (8327:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8654
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8655) ≤ val WuPaper.ClassicalFourthData.Bq 8655
    have hp : val WuPaper.ClassicalFourthData.Bq 8655 = (276615558783940:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8655 = 276615558783940 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8655 = (3331:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8655
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_540
