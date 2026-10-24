import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints599
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_599 (j : Fin 16) (hj : 16*599+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*599+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*599+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9584) ≤ val WuPaper.ClassicalFourthData.Bq 9584
    have hp : val WuPaper.ClassicalFourthData.Bq 9584 = (278116075636471:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9584 = 278116075636471 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9584 = (1099:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9584
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9585) ≤ val WuPaper.ClassicalFourthData.Bq 9585
    have hp : val WuPaper.ClassicalFourthData.Bq 9585 = (278117004676105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9585 = 278117004676105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9585 = (3517:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9585
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9586) ≤ val WuPaper.ClassicalFourthData.Bq 9586
    have hp : val WuPaper.ClassicalFourthData.Bq 9586 = (278117932377621:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9586 = 278117932377621 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9586 = (8793:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9586
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9587) ≤ val WuPaper.ClassicalFourthData.Bq 9587
    have hp : val WuPaper.ClassicalFourthData.Bq 9587 = (278118858741426:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9587 = 278118858741426 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9587 = (17587:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9587
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9588) ≤ val WuPaper.ClassicalFourthData.Bq 9588
    have hp : val WuPaper.ClassicalFourthData.Bq 9588 = (278119783767932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9588 = 278119783767932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9588 = (4397:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9588
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9589) ≤ val WuPaper.ClassicalFourthData.Bq 9589
    have hp : val WuPaper.ClassicalFourthData.Bq 9589 = (278120707457548:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9589 = 278120707457548 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9589 = (17589:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9589
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9590) ≤ val WuPaper.ClassicalFourthData.Bq 9590
    have hp : val WuPaper.ClassicalFourthData.Bq 9590 = (278121629810682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9590 = 278121629810682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9590 = (1759:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9590
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9591) ≤ val WuPaper.ClassicalFourthData.Bq 9591
    have hp : val WuPaper.ClassicalFourthData.Bq 9591 = (278122550827745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9591 = 278122550827745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9591 = (17591:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9591
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9592) ≤ val WuPaper.ClassicalFourthData.Bq 9592
    have hp : val WuPaper.ClassicalFourthData.Bq 9592 = (278123470509144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9592 = 278123470509144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9592 = (2199:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9592
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9593) ≤ val WuPaper.ClassicalFourthData.Bq 9593
    have hp : val WuPaper.ClassicalFourthData.Bq 9593 = (278124388855290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9593 = 278124388855290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9593 = (17593:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9593
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9594) ≤ val WuPaper.ClassicalFourthData.Bq 9594
    have hp : val WuPaper.ClassicalFourthData.Bq 9594 = (278125305866590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9594 = 278125305866590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9594 = (8797:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9594
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9595) ≤ val WuPaper.ClassicalFourthData.Bq 9595
    have hp : val WuPaper.ClassicalFourthData.Bq 9595 = (278126221543453:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9595 = 278126221543453 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9595 = (3519:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9595
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9596) ≤ val WuPaper.ClassicalFourthData.Bq 9596
    have hp : val WuPaper.ClassicalFourthData.Bq 9596 = (278127135886289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9596 = 278127135886289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9596 = (4399:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9596
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9597) ≤ val WuPaper.ClassicalFourthData.Bq 9597
    have hp : val WuPaper.ClassicalFourthData.Bq 9597 = (278128048895504:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9597 = 278128048895504 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9597 = (17597:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9597
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9598) ≤ val WuPaper.ClassicalFourthData.Bq 9598
    have hp : val WuPaper.ClassicalFourthData.Bq 9598 = (278128960571507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9598 = 278128960571507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9598 = (8799:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9598
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9599) ≤ val WuPaper.ClassicalFourthData.Bq 9599
    have hp : val WuPaper.ClassicalFourthData.Bq 9599 = (278129870914707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9599 = 278129870914707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9599 = (17599:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9599
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_599
