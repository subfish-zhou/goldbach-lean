import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints485
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_485 (j : Fin 16) (hj : 16*485+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*485+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*485+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7760) ≤ val WuPaper.ClassicalFourthData.Bq 7760
    have hp : val WuPaper.ClassicalFourthData.Bq 7760 = (273708015571603:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7760 = 273708015571603 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7760 = (197:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7760
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7761) ≤ val WuPaper.ClassicalFourthData.Bq 7761
    have hp : val WuPaper.ClassicalFourthData.Bq 7761 = (273712229363756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7761 = 273712229363756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7761 = (15761:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7761
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7762) ≤ val WuPaper.ClassicalFourthData.Bq 7762
    have hp : val WuPaper.ClassicalFourthData.Bq 7762 = (273716440786551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7762 = 273716440786551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7762 = (7881:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7762
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7763) ≤ val WuPaper.ClassicalFourthData.Bq 7763
    have hp : val WuPaper.ClassicalFourthData.Bq 7763 = (273720649840753:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7763 = 273720649840753 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7763 = (15763:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7763
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7764) ≤ val WuPaper.ClassicalFourthData.Bq 7764
    have hp : val WuPaper.ClassicalFourthData.Bq 7764 = (273724856527124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7764 = 273724856527124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7764 = (3941:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7764
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7765) ≤ val WuPaper.ClassicalFourthData.Bq 7765
    have hp : val WuPaper.ClassicalFourthData.Bq 7765 = (273729060846426:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7765 = 273729060846426 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7765 = (3153:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7765
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7766) ≤ val WuPaper.ClassicalFourthData.Bq 7766
    have hp : val WuPaper.ClassicalFourthData.Bq 7766 = (273733262799421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7766 = 273733262799421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7766 = (7883:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7766
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7767) ≤ val WuPaper.ClassicalFourthData.Bq 7767
    have hp : val WuPaper.ClassicalFourthData.Bq 7767 = (273737462386871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7767 = 273737462386871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7767 = (15767:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7767
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7768) ≤ val WuPaper.ClassicalFourthData.Bq 7768
    have hp : val WuPaper.ClassicalFourthData.Bq 7768 = (273741659609538:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7768 = 273741659609538 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7768 = (1971:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7768
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7769) ≤ val WuPaper.ClassicalFourthData.Bq 7769
    have hp : val WuPaper.ClassicalFourthData.Bq 7769 = (273745854468182:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7769 = 273745854468182 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7769 = (15769:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7769
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7770) ≤ val WuPaper.ClassicalFourthData.Bq 7770
    have hp : val WuPaper.ClassicalFourthData.Bq 7770 = (273750046963565:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7770 = 273750046963565 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7770 = (1577:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7770
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7771) ≤ val WuPaper.ClassicalFourthData.Bq 7771
    have hp : val WuPaper.ClassicalFourthData.Bq 7771 = (273754237096447:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7771 = 273754237096447 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7771 = (15771:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7771
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7772) ≤ val WuPaper.ClassicalFourthData.Bq 7772
    have hp : val WuPaper.ClassicalFourthData.Bq 7772 = (273758424867589:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7772 = 273758424867589 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7772 = (3943:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7772
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7773) ≤ val WuPaper.ClassicalFourthData.Bq 7773
    have hp : val WuPaper.ClassicalFourthData.Bq 7773 = (273762610277750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7773 = 273762610277750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7773 = (15773:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7773
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7774) ≤ val WuPaper.ClassicalFourthData.Bq 7774
    have hp : val WuPaper.ClassicalFourthData.Bq 7774 = (273766793327692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7774 = 273766793327692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7774 = (7887:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7774
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7775) ≤ val WuPaper.ClassicalFourthData.Bq 7775
    have hp : val WuPaper.ClassicalFourthData.Bq 7775 = (273770974018172:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7775 = 273770974018172 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7775 = (631:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7775
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_485
