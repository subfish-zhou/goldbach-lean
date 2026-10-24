import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints033
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_033 (j : Fin 16) (hj : 16*33+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*33+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*33+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 528) ≤ val WuPaper.ClassicalFourthData.Bq 528
    have hp : val WuPaper.ClassicalFourthData.Bq 528 = (58154774756563:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 528 = 58154774756563 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 528 = (533:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_528
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 529) ≤ val WuPaper.ClassicalFourthData.Bq 529
    have hp : val WuPaper.ClassicalFourthData.Bq 529 = (58251519969135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 529 = 58251519969135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 529 = (8529:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_529
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 530) ≤ val WuPaper.ClassicalFourthData.Bq 530
    have hp : val WuPaper.ClassicalFourthData.Bq 530 = (58348219636602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 530 = 58348219636602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 530 = (853:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_530
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 531) ≤ val WuPaper.ClassicalFourthData.Bq 531
    have hp : val WuPaper.ClassicalFourthData.Bq 531 = (58444873785072:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 531 = 58444873785072 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 531 = (8531:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_531
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 532) ≤ val WuPaper.ClassicalFourthData.Bq 532
    have hp : val WuPaper.ClassicalFourthData.Bq 532 = (58541482440633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 532 = 58541482440633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 532 = (2133:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_532
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 533) ≤ val WuPaper.ClassicalFourthData.Bq 533
    have hp : val WuPaper.ClassicalFourthData.Bq 533 = (58638045629356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 533 = 58638045629356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 533 = (8533:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_533
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 534) ≤ val WuPaper.ClassicalFourthData.Bq 534
    have hp : val WuPaper.ClassicalFourthData.Bq 534 = (58734563377290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 534 = 58734563377290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 534 = (4267:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_534
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 535) ≤ val WuPaper.ClassicalFourthData.Bq 535
    have hp : val WuPaper.ClassicalFourthData.Bq 535 = (58831035710468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 535 = 58831035710468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 535 = (1707:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_535
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 536) ≤ val WuPaper.ClassicalFourthData.Bq 536
    have hp : val WuPaper.ClassicalFourthData.Bq 536 = (58927462654902:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 536 = 58927462654902 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 536 = (1067:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_536
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 537) ≤ val WuPaper.ClassicalFourthData.Bq 537
    have hp : val WuPaper.ClassicalFourthData.Bq 537 = (59023844236588:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 537 = 59023844236588 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 537 = (8537:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_537
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 538) ≤ val WuPaper.ClassicalFourthData.Bq 538
    have hp : val WuPaper.ClassicalFourthData.Bq 538 = (59120180481499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 538 = 59120180481499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 538 = (4269:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_538
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 539) ≤ val WuPaper.ClassicalFourthData.Bq 539
    have hp : val WuPaper.ClassicalFourthData.Bq 539 = (59216471415594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 539 = 59216471415594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 539 = (8539:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_539
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 540) ≤ val WuPaper.ClassicalFourthData.Bq 540
    have hp : val WuPaper.ClassicalFourthData.Bq 540 = (59312717064809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 540 = 59312717064809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 540 = (427:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_540
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 541) ≤ val WuPaper.ClassicalFourthData.Bq 541
    have hp : val WuPaper.ClassicalFourthData.Bq 541 = (59408917455064:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 541 = 59408917455064 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 541 = (8541:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_541
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 542) ≤ val WuPaper.ClassicalFourthData.Bq 542
    have hp : val WuPaper.ClassicalFourthData.Bq 542 = (59505072612258:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 542 = 59505072612258 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 542 = (4271:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_542
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 543) ≤ val WuPaper.ClassicalFourthData.Bq 543
    have hp : val WuPaper.ClassicalFourthData.Bq 543 = (59601182562274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 543 = 59601182562274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 543 = (8543:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_543
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_033
