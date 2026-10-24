import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints605
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_605 (j : Fin 16) (hj : 16*605+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*605+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*605+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9680) ≤ val WuPaper.ClassicalFourthData.Bq 9680
    have hp : val WuPaper.ClassicalFourthData.Bq 9680 = (278199219713049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9680 = 278199219713049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9680 = (221:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9680
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9681) ≤ val WuPaper.ClassicalFourthData.Bq 9681
    have hp : val WuPaper.ClassicalFourthData.Bq 9681 = (278200022142490:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9681 = 278200022142490 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9681 = (17681:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9681
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9682) ≤ val WuPaper.ClassicalFourthData.Bq 9682
    have hp : val WuPaper.ClassicalFourthData.Bq 9682 = (278200823272540:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9682 = 278200823272540 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9682 = (8841:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9682
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9683) ≤ val WuPaper.ClassicalFourthData.Bq 9683
    have hp : val WuPaper.ClassicalFourthData.Bq 9683 = (278201623103596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9683 = 278201623103596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9683 = (17683:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9683
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9684) ≤ val WuPaper.ClassicalFourthData.Bq 9684
    have hp : val WuPaper.ClassicalFourthData.Bq 9684 = (278202421636056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9684 = 278202421636056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9684 = (4421:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9684
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9685) ≤ val WuPaper.ClassicalFourthData.Bq 9685
    have hp : val WuPaper.ClassicalFourthData.Bq 9685 = (278203218870315:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9685 = 278203218870315 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9685 = (3537:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9685
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9686) ≤ val WuPaper.ClassicalFourthData.Bq 9686
    have hp : val WuPaper.ClassicalFourthData.Bq 9686 = (278204014806771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9686 = 278204014806771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9686 = (8843:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9686
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9687) ≤ val WuPaper.ClassicalFourthData.Bq 9687
    have hp : val WuPaper.ClassicalFourthData.Bq 9687 = (278204809445820:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9687 = 278204809445820 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9687 = (17687:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9687
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9688) ≤ val WuPaper.ClassicalFourthData.Bq 9688
    have hp : val WuPaper.ClassicalFourthData.Bq 9688 = (278205602787859:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9688 = 278205602787859 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9688 = (2211:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9688
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9689) ≤ val WuPaper.ClassicalFourthData.Bq 9689
    have hp : val WuPaper.ClassicalFourthData.Bq 9689 = (278206394833284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9689 = 278206394833284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9689 = (17689:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9689
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9690) ≤ val WuPaper.ClassicalFourthData.Bq 9690
    have hp : val WuPaper.ClassicalFourthData.Bq 9690 = (278207185582491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9690 = 278207185582491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9690 = (1769:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9690
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9691) ≤ val WuPaper.ClassicalFourthData.Bq 9691
    have hp : val WuPaper.ClassicalFourthData.Bq 9691 = (278207975035877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9691 = 278207975035877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9691 = (17691:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9691
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9692) ≤ val WuPaper.ClassicalFourthData.Bq 9692
    have hp : val WuPaper.ClassicalFourthData.Bq 9692 = (278208763193836:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9692 = 278208763193836 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9692 = (4423:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9692
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9693) ≤ val WuPaper.ClassicalFourthData.Bq 9693
    have hp : val WuPaper.ClassicalFourthData.Bq 9693 = (278209550056766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9693 = 278209550056766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9693 = (17693:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9693
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9694) ≤ val WuPaper.ClassicalFourthData.Bq 9694
    have hp : val WuPaper.ClassicalFourthData.Bq 9694 = (278210335625062:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9694 = 278210335625062 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9694 = (8847:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9694
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9695) ≤ val WuPaper.ClassicalFourthData.Bq 9695
    have hp : val WuPaper.ClassicalFourthData.Bq 9695 = (278211119899119:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9695 = 278211119899119 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9695 = (3539:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9695
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_605
