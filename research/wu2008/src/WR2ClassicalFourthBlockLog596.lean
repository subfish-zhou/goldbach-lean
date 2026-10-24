import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints596
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_596 (j : Fin 16) (hj : 16*596+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*596+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*596+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9536) ≤ val WuPaper.ClassicalFourthData.Bq 9536
    have hp : val WuPaper.ClassicalFourthData.Bq 9536 = (278069900043127:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9536 = 278069900043127 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9536 = (548:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9536
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9537) ≤ val WuPaper.ClassicalFourthData.Bq 9537
    have hp : val WuPaper.ClassicalFourthData.Bq 9537 = (278070893796870:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9537 = 278070893796870 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9537 = (17537:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9537
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9538) ≤ val WuPaper.ClassicalFourthData.Bq 9538
    have hp : val WuPaper.ClassicalFourthData.Bq 9538 = (278071886192671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9538 = 278071886192671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9538 = (8769:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9538
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9539) ≤ val WuPaper.ClassicalFourthData.Bq 9539
    have hp : val WuPaper.ClassicalFourthData.Bq 9539 = (278072877230948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9539 = 278072877230948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9539 = (17539:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9539
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9540) ≤ val WuPaper.ClassicalFourthData.Bq 9540
    have hp : val WuPaper.ClassicalFourthData.Bq 9540 = (278073866912116:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9540 = 278073866912116 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9540 = (877:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9540
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9541) ≤ val WuPaper.ClassicalFourthData.Bq 9541
    have hp : val WuPaper.ClassicalFourthData.Bq 9541 = (278074855236592:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9541 = 278074855236592 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9541 = (17541:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9541
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9542) ≤ val WuPaper.ClassicalFourthData.Bq 9542
    have hp : val WuPaper.ClassicalFourthData.Bq 9542 = (278075842204790:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9542 = 278075842204790 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9542 = (8771:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9542
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9543) ≤ val WuPaper.ClassicalFourthData.Bq 9543
    have hp : val WuPaper.ClassicalFourthData.Bq 9543 = (278076827817127:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9543 = 278076827817127 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9543 = (17543:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9543
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9544) ≤ val WuPaper.ClassicalFourthData.Bq 9544
    have hp : val WuPaper.ClassicalFourthData.Bq 9544 = (278077812074017:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9544 = 278077812074017 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9544 = (2193:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9544
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9545) ≤ val WuPaper.ClassicalFourthData.Bq 9545
    have hp : val WuPaper.ClassicalFourthData.Bq 9545 = (278078794975877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9545 = 278078794975877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9545 = (3509:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9545
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9546) ≤ val WuPaper.ClassicalFourthData.Bq 9546
    have hp : val WuPaper.ClassicalFourthData.Bq 9546 = (278079776523121:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9546 = 278079776523121 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9546 = (8773:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9546
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9547) ≤ val WuPaper.ClassicalFourthData.Bq 9547
    have hp : val WuPaper.ClassicalFourthData.Bq 9547 = (278080756716164:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9547 = 278080756716164 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9547 = (17547:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9547
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9548) ≤ val WuPaper.ClassicalFourthData.Bq 9548
    have hp : val WuPaper.ClassicalFourthData.Bq 9548 = (278081735555422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9548 = 278081735555422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9548 = (4387:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9548
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9549) ≤ val WuPaper.ClassicalFourthData.Bq 9549
    have hp : val WuPaper.ClassicalFourthData.Bq 9549 = (278082713041308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9549 = 278082713041308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9549 = (17549:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9549
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9550) ≤ val WuPaper.ClassicalFourthData.Bq 9550
    have hp : val WuPaper.ClassicalFourthData.Bq 9550 = (278083689174239:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9550 = 278083689174239 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9550 = (351:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9550
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9551) ≤ val WuPaper.ClassicalFourthData.Bq 9551
    have hp : val WuPaper.ClassicalFourthData.Bq 9551 = (278084663954627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9551 = 278084663954627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9551 = (17551:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9551
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_596
