import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints604
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_604 (j : Fin 16) (hj : 16*604+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*604+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*604+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9664) ≤ val WuPaper.ClassicalFourthData.Bq 9664
    have hp : val WuPaper.ClassicalFourthData.Bq 9664 = (278186203800274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9664 = 278186203800274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9664 = (552:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9664
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9665) ≤ val WuPaper.ClassicalFourthData.Bq 9665
    have hp : val WuPaper.ClassicalFourthData.Bq 9665 = (278187027074083:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9665 = 278187027074083 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9665 = (3533:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9665
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9666) ≤ val WuPaper.ClassicalFourthData.Bq 9666
    have hp : val WuPaper.ClassicalFourthData.Bq 9666 = (278187849042130:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9666 = 278187849042130 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9666 = (8833:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9666
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9667) ≤ val WuPaper.ClassicalFourthData.Bq 9667
    have hp : val WuPaper.ClassicalFourthData.Bq 9667 = (278188669704813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9667 = 278188669704813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9667 = (17667:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9667
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9668) ≤ val WuPaper.ClassicalFourthData.Bq 9668
    have hp : val WuPaper.ClassicalFourthData.Bq 9668 = (278189489062533:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9668 = 278189489062533 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9668 = (4417:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9668
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9669) ≤ val WuPaper.ClassicalFourthData.Bq 9669
    have hp : val WuPaper.ClassicalFourthData.Bq 9669 = (278190307115687:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9669 = 278190307115687 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9669 = (17669:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9669
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9670) ≤ val WuPaper.ClassicalFourthData.Bq 9670
    have hp : val WuPaper.ClassicalFourthData.Bq 9670 = (278191123864675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9670 = 278191123864675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9670 = (1767:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9670
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9671) ≤ val WuPaper.ClassicalFourthData.Bq 9671
    have hp : val WuPaper.ClassicalFourthData.Bq 9671 = (278191939309896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9671 = 278191939309896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9671 = (17671:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9671
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9672) ≤ val WuPaper.ClassicalFourthData.Bq 9672
    have hp : val WuPaper.ClassicalFourthData.Bq 9672 = (278192753451747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9672 = 278192753451747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9672 = (2209:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9672
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9673) ≤ val WuPaper.ClassicalFourthData.Bq 9673
    have hp : val WuPaper.ClassicalFourthData.Bq 9673 = (278193566290628:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9673 = 278193566290628 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9673 = (17673:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9673
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9674) ≤ val WuPaper.ClassicalFourthData.Bq 9674
    have hp : val WuPaper.ClassicalFourthData.Bq 9674 = (278194377826936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9674 = 278194377826936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9674 = (8837:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9674
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9675) ≤ val WuPaper.ClassicalFourthData.Bq 9675
    have hp : val WuPaper.ClassicalFourthData.Bq 9675 = (278195188061070:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9675 = 278195188061070 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9675 = (707:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9675
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9676) ≤ val WuPaper.ClassicalFourthData.Bq 9676
    have hp : val WuPaper.ClassicalFourthData.Bq 9676 = (278195996993427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9676 = 278195996993427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9676 = (4419:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9676
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9677) ≤ val WuPaper.ClassicalFourthData.Bq 9677
    have hp : val WuPaper.ClassicalFourthData.Bq 9677 = (278196804624406:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9677 = 278196804624406 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9677 = (17677:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9677
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9678) ≤ val WuPaper.ClassicalFourthData.Bq 9678
    have hp : val WuPaper.ClassicalFourthData.Bq 9678 = (278197610954404:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9678 = 278197610954404 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9678 = (8839:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9678
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9679) ≤ val WuPaper.ClassicalFourthData.Bq 9679
    have hp : val WuPaper.ClassicalFourthData.Bq 9679 = (278198415983819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9679 = 278198415983819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9679 = (17679:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9679
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_604
