import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints036
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_036 (j : Fin 16) (hj : 16*36+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*36+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*36+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 576) ≤ val WuPaper.ClassicalFourthData.Bq 576
    have hp : val WuPaper.ClassicalFourthData.Bq 576 = (62747617983959:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 576 = 62747617983959 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 576 = (268:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_576
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 577) ≤ val WuPaper.ClassicalFourthData.Bq 577
    have hp : val WuPaper.ClassicalFourthData.Bq 577 = (62842206156752:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 577 = 62842206156752 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 577 = (8577:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_577
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 578) ≤ val WuPaper.ClassicalFourthData.Bq 578
    have hp : val WuPaper.ClassicalFourthData.Bq 578 = (62936750016547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 578 = 62936750016547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 578 = (4289:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_578
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 579) ≤ val WuPaper.ClassicalFourthData.Bq 579
    have hp : val WuPaper.ClassicalFourthData.Bq 579 = (63031249588562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 579 = 63031249588562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 579 = (8579:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_579
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 580) ≤ val WuPaper.ClassicalFourthData.Bq 580
    have hp : val WuPaper.ClassicalFourthData.Bq 580 = (63125704897997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 580 = 63125704897997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 580 = (429:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_580
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 581) ≤ val WuPaper.ClassicalFourthData.Bq 581
    have hp : val WuPaper.ClassicalFourthData.Bq 581 = (63220115970034:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 581 = 63220115970034 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 581 = (8581:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_581
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 582) ≤ val WuPaper.ClassicalFourthData.Bq 582
    have hp : val WuPaper.ClassicalFourthData.Bq 582 = (63314482829837:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 582 = 63314482829837 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 582 = (4291:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_582
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 583) ≤ val WuPaper.ClassicalFourthData.Bq 583
    have hp : val WuPaper.ClassicalFourthData.Bq 583 = (63408805502550:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 583 = 63408805502550 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 583 = (8583:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_583
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 584) ≤ val WuPaper.ClassicalFourthData.Bq 584
    have hp : val WuPaper.ClassicalFourthData.Bq 584 = (63503084013303:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 584 = 63503084013303 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 584 = (1073:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_584
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 585) ≤ val WuPaper.ClassicalFourthData.Bq 585
    have hp : val WuPaper.ClassicalFourthData.Bq 585 = (63597318387205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 585 = 63597318387205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 585 = (1717:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_585
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 586) ≤ val WuPaper.ClassicalFourthData.Bq 586
    have hp : val WuPaper.ClassicalFourthData.Bq 586 = (63691508649347:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 586 = 63691508649347 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 586 = (4293:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_586
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 587) ≤ val WuPaper.ClassicalFourthData.Bq 587
    have hp : val WuPaper.ClassicalFourthData.Bq 587 = (63785654824803:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 587 = 63785654824803 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 587 = (8587:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_587
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 588) ≤ val WuPaper.ClassicalFourthData.Bq 588
    have hp : val WuPaper.ClassicalFourthData.Bq 588 = (63879756938628:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 588 = 63879756938628 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 588 = (2147:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_588
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 589) ≤ val WuPaper.ClassicalFourthData.Bq 589
    have hp : val WuPaper.ClassicalFourthData.Bq 589 = (63973815015861:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 589 = 63973815015861 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 589 = (8589:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_589
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 590) ≤ val WuPaper.ClassicalFourthData.Bq 590
    have hp : val WuPaper.ClassicalFourthData.Bq 590 = (64067829081520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 590 = 64067829081520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 590 = (859:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_590
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 591) ≤ val WuPaper.ClassicalFourthData.Bq 591
    have hp : val WuPaper.ClassicalFourthData.Bq 591 = (64161799160608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 591 = 64161799160608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 591 = (8591:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_591
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_036
