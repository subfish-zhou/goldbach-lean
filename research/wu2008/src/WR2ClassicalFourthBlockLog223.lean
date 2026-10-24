import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints223
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_223 (j : Fin 16) (hj : 16*223+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*223+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*223+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3568) ≤ val WuPaper.ClassicalFourthData.Bq 3568
    have hp : val WuPaper.ClassicalFourthData.Bq 3568 = (220482182098786:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3568 = 220482182098786 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3568 = (723:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3568
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3569) ≤ val WuPaper.ClassicalFourthData.Bq 3569
    have hp : val WuPaper.ClassicalFourthData.Bq 3569 = (220508807055801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3569 = 220508807055801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3569 = (11569:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3569
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3570) ≤ val WuPaper.ClassicalFourthData.Bq 3570
    have hp : val WuPaper.ClassicalFourthData.Bq 3570 = (220535421375789:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3570 = 220535421375789 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3570 = (1157:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3570
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3571) ≤ val WuPaper.ClassicalFourthData.Bq 3571
    have hp : val WuPaper.ClassicalFourthData.Bq 3571 = (220562025063099:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3571 = 220562025063099 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3571 = (11571:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3571
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3572) ≤ val WuPaper.ClassicalFourthData.Bq 3572
    have hp : val WuPaper.ClassicalFourthData.Bq 3572 = (220588618122083:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3572 = 220588618122083 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3572 = (2893:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3572
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3573) ≤ val WuPaper.ClassicalFourthData.Bq 3573
    have hp : val WuPaper.ClassicalFourthData.Bq 3573 = (220615200557089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3573 = 220615200557089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3573 = (11573:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3573
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3574) ≤ val WuPaper.ClassicalFourthData.Bq 3574
    have hp : val WuPaper.ClassicalFourthData.Bq 3574 = (220641772372460:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3574 = 220641772372460 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3574 = (5787:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3574
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3575) ≤ val WuPaper.ClassicalFourthData.Bq 3575
    have hp : val WuPaper.ClassicalFourthData.Bq 3575 = (220668333572542:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3575 = 220668333572542 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3575 = (463:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3575
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3576) ≤ val WuPaper.ClassicalFourthData.Bq 3576
    have hp : val WuPaper.ClassicalFourthData.Bq 3576 = (220694884161675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3576 = 220694884161675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3576 = (1447:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3576
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3577) ≤ val WuPaper.ClassicalFourthData.Bq 3577
    have hp : val WuPaper.ClassicalFourthData.Bq 3577 = (220721424144199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3577 = 220721424144199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3577 = (11577:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3577
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3578) ≤ val WuPaper.ClassicalFourthData.Bq 3578
    have hp : val WuPaper.ClassicalFourthData.Bq 3578 = (220747953524450:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3578 = 220747953524450 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3578 = (5789:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3578
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3579) ≤ val WuPaper.ClassicalFourthData.Bq 3579
    have hp : val WuPaper.ClassicalFourthData.Bq 3579 = (220774472306763:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3579 = 220774472306763 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3579 = (11579:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3579
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3580) ≤ val WuPaper.ClassicalFourthData.Bq 3580
    have hp : val WuPaper.ClassicalFourthData.Bq 3580 = (220800980495472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3580 = 220800980495472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3580 = (579:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3580
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3581) ≤ val WuPaper.ClassicalFourthData.Bq 3581
    have hp : val WuPaper.ClassicalFourthData.Bq 3581 = (220827478094906:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3581 = 220827478094906 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3581 = (11581:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3581
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3582) ≤ val WuPaper.ClassicalFourthData.Bq 3582
    have hp : val WuPaper.ClassicalFourthData.Bq 3582 = (220853965109395:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3582 = 220853965109395 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3582 = (5791:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3582
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3583) ≤ val WuPaper.ClassicalFourthData.Bq 3583
    have hp : val WuPaper.ClassicalFourthData.Bq 3583 = (220880441543265:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3583 = 220880441543265 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3583 = (11583:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3583
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_223
