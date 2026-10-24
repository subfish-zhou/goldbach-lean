import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints355
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_355 (j : Fin 16) (hj : 16*355+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*355+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*355+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5680) ≤ val WuPaper.ClassicalFourthData.Bq 5680
    have hp : val WuPaper.ClassicalFourthData.Bq 5680 = (258411561452808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5680 = 258411561452808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5680 = (171:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5680
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5681) ≤ val WuPaper.ClassicalFourthData.Bq 5681
    have hp : val WuPaper.ClassicalFourthData.Bq 5681 = (258422875701499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5681 = 258422875701499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5681 = (13681:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5681
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5682) ≤ val WuPaper.ClassicalFourthData.Bq 5682
    have hp : val WuPaper.ClassicalFourthData.Bq 5682 = (258434185176910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5682 = 258434185176910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5682 = (6841:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5682
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5683) ≤ val WuPaper.ClassicalFourthData.Bq 5683
    have hp : val WuPaper.ClassicalFourthData.Bq 5683 = (258445489880731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5683 = 258445489880731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5683 = (13683:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5683
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5684) ≤ val WuPaper.ClassicalFourthData.Bq 5684
    have hp : val WuPaper.ClassicalFourthData.Bq 5684 = (258456789814653:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5684 = 258456789814653 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5684 = (3421:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5684
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5685) ≤ val WuPaper.ClassicalFourthData.Bq 5685
    have hp : val WuPaper.ClassicalFourthData.Bq 5685 = (258468084980366:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5685 = 258468084980366 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5685 = (2737:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5685
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5686) ≤ val WuPaper.ClassicalFourthData.Bq 5686
    have hp : val WuPaper.ClassicalFourthData.Bq 5686 = (258479375379557:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5686 = 258479375379557 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5686 = (6843:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5686
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5687) ≤ val WuPaper.ClassicalFourthData.Bq 5687
    have hp : val WuPaper.ClassicalFourthData.Bq 5687 = (258490661013915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5687 = 258490661013915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5687 = (13687:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5687
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5688) ≤ val WuPaper.ClassicalFourthData.Bq 5688
    have hp : val WuPaper.ClassicalFourthData.Bq 5688 = (258501941885128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5688 = 258501941885128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5688 = (1711:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5688
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5689) ≤ val WuPaper.ClassicalFourthData.Bq 5689
    have hp : val WuPaper.ClassicalFourthData.Bq 5689 = (258513217994882:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5689 = 258513217994882 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5689 = (13689:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5689
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5690) ≤ val WuPaper.ClassicalFourthData.Bq 5690
    have hp : val WuPaper.ClassicalFourthData.Bq 5690 = (258524489344863:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5690 = 258524489344863 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5690 = (1369:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5690
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5691) ≤ val WuPaper.ClassicalFourthData.Bq 5691
    have hp : val WuPaper.ClassicalFourthData.Bq 5691 = (258535755936756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5691 = 258535755936756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5691 = (13691:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5691
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5692) ≤ val WuPaper.ClassicalFourthData.Bq 5692
    have hp : val WuPaper.ClassicalFourthData.Bq 5692 = (258547017772246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5692 = 258547017772246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5692 = (3423:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5692
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5693) ≤ val WuPaper.ClassicalFourthData.Bq 5693
    have hp : val WuPaper.ClassicalFourthData.Bq 5693 = (258558274853016:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5693 = 258558274853016 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5693 = (13693:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5693
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5694) ≤ val WuPaper.ClassicalFourthData.Bq 5694
    have hp : val WuPaper.ClassicalFourthData.Bq 5694 = (258569527180751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5694 = 258569527180751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5694 = (6847:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5694
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5695) ≤ val WuPaper.ClassicalFourthData.Bq 5695
    have hp : val WuPaper.ClassicalFourthData.Bq 5695 = (258580774757133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5695 = 258580774757133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5695 = (2739:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5695
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_355
