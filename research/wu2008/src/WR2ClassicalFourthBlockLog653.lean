import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints653
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_653 (j : Fin 16) (hj : 16*653+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*653+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*653+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10448) ≤ val WuPaper.ClassicalFourthData.Bq 10448
    have hp : val WuPaper.ClassicalFourthData.Bq 10448 = (278460892398600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10448 = 278460892398600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10448 = (1153:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10448
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10449) ≤ val WuPaper.ClassicalFourthData.Bq 10449
    have hp : val WuPaper.ClassicalFourthData.Bq 10449 = (278460804830498:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10449 = 278460804830498 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10449 = (18449:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10449
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10450) ≤ val WuPaper.ClassicalFourthData.Bq 10450
    have hp : val WuPaper.ClassicalFourthData.Bq 10450 = (278460716233432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10450 = 278460716233432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10450 = (369:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10450
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10451) ≤ val WuPaper.ClassicalFourthData.Bq 10451
    have hp : val WuPaper.ClassicalFourthData.Bq 10451 = (278460626607715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10451 = 278460626607715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10451 = (18451:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10451
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10452) ≤ val WuPaper.ClassicalFourthData.Bq 10452
    have hp : val WuPaper.ClassicalFourthData.Bq 10452 = (278460535953656:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10452 = 278460535953656 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10452 = (4613:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10452
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10453) ≤ val WuPaper.ClassicalFourthData.Bq 10453
    have hp : val WuPaper.ClassicalFourthData.Bq 10453 = (278460444271566:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10453 = 278460444271566 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10453 = (18453:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10453
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10454) ≤ val WuPaper.ClassicalFourthData.Bq 10454
    have hp : val WuPaper.ClassicalFourthData.Bq 10454 = (278460351561756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10454 = 278460351561756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10454 = (9227:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10454
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10455) ≤ val WuPaper.ClassicalFourthData.Bq 10455
    have hp : val WuPaper.ClassicalFourthData.Bq 10455 = (278460257824538:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10455 = 278460257824538 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10455 = (3691:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10455
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10456) ≤ val WuPaper.ClassicalFourthData.Bq 10456
    have hp : val WuPaper.ClassicalFourthData.Bq 10456 = (278460163060221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10456 = 278460163060221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10456 = (2307:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10456
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10457) ≤ val WuPaper.ClassicalFourthData.Bq 10457
    have hp : val WuPaper.ClassicalFourthData.Bq 10457 = (278460067269115:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10457 = 278460067269115 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10457 = (18457:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10457
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10458) ≤ val WuPaper.ClassicalFourthData.Bq 10458
    have hp : val WuPaper.ClassicalFourthData.Bq 10458 = (278459970451532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10458 = 278459970451532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10458 = (9229:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10458
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10459) ≤ val WuPaper.ClassicalFourthData.Bq 10459
    have hp : val WuPaper.ClassicalFourthData.Bq 10459 = (278459872607781:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10459 = 278459872607781 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10459 = (18459:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10459
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10460) ≤ val WuPaper.ClassicalFourthData.Bq 10460
    have hp : val WuPaper.ClassicalFourthData.Bq 10460 = (278459773738173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10460 = 278459773738173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10460 = (923:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10460
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10461) ≤ val WuPaper.ClassicalFourthData.Bq 10461
    have hp : val WuPaper.ClassicalFourthData.Bq 10461 = (278459673843017:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10461 = 278459673843017 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10461 = (18461:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10461
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10462) ≤ val WuPaper.ClassicalFourthData.Bq 10462
    have hp : val WuPaper.ClassicalFourthData.Bq 10462 = (278459572922623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10462 = 278459572922623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10462 = (9231:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10462
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10463) ≤ val WuPaper.ClassicalFourthData.Bq 10463
    have hp : val WuPaper.ClassicalFourthData.Bq 10463 = (278459470977303:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10463 = 278459470977303 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10463 = (18463:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10463
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_653
