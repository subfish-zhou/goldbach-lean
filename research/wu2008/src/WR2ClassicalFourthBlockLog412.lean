import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints412
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_412 (j : Fin 16) (hj : 16*412+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*412+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*412+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6592) ≤ val WuPaper.ClassicalFourthData.Bq 6592
    have hp : val WuPaper.ClassicalFourthData.Bq 6592 = (266942060875782:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6592 = 266942060875782 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6592 = (456:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6592
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6593) ≤ val WuPaper.ClassicalFourthData.Bq 6593
    have hp : val WuPaper.ClassicalFourthData.Bq 6593 = (266949645582008:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6593 = 266949645582008 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6593 = (14593:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6593
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6594) ≤ val WuPaper.ClassicalFourthData.Bq 6594
    have hp : val WuPaper.ClassicalFourthData.Bq 6594 = (266957226806231:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6594 = 266957226806231 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6594 = (7297:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6594
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6595) ≤ val WuPaper.ClassicalFourthData.Bq 6595
    have hp : val WuPaper.ClassicalFourthData.Bq 6595 = (266964804549630:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6595 = 266964804549630 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6595 = (2919:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6595
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6596) ≤ val WuPaper.ClassicalFourthData.Bq 6596
    have hp : val WuPaper.ClassicalFourthData.Bq 6596 = (266972378813380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6596 = 266972378813380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6596 = (3649:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6596
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6597) ≤ val WuPaper.ClassicalFourthData.Bq 6597
    have hp : val WuPaper.ClassicalFourthData.Bq 6597 = (266979949598657:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6597 = 266979949598657 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6597 = (14597:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6597
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6598) ≤ val WuPaper.ClassicalFourthData.Bq 6598
    have hp : val WuPaper.ClassicalFourthData.Bq 6598 = (266987516906637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6598 = 266987516906637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6598 = (7299:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6598
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6599) ≤ val WuPaper.ClassicalFourthData.Bq 6599
    have hp : val WuPaper.ClassicalFourthData.Bq 6599 = (266995080738494:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6599 = 266995080738494 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6599 = (14599:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6599
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6600) ≤ val WuPaper.ClassicalFourthData.Bq 6600
    have hp : val WuPaper.ClassicalFourthData.Bq 6600 = (267002641095404:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6600 = 267002641095404 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6600 = (73:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6600
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6601) ≤ val WuPaper.ClassicalFourthData.Bq 6601
    have hp : val WuPaper.ClassicalFourthData.Bq 6601 = (267010197978539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6601 = 267010197978539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6601 = (14601:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6601
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6602) ≤ val WuPaper.ClassicalFourthData.Bq 6602
    have hp : val WuPaper.ClassicalFourthData.Bq 6602 = (267017751389075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6602 = 267017751389075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6602 = (7301:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6602
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6603) ≤ val WuPaper.ClassicalFourthData.Bq 6603
    have hp : val WuPaper.ClassicalFourthData.Bq 6603 = (267025301328183:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6603 = 267025301328183 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6603 = (14603:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6603
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6604) ≤ val WuPaper.ClassicalFourthData.Bq 6604
    have hp : val WuPaper.ClassicalFourthData.Bq 6604 = (267032847797037:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6604 = 267032847797037 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6604 = (3651:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6604
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6605) ≤ val WuPaper.ClassicalFourthData.Bq 6605
    have hp : val WuPaper.ClassicalFourthData.Bq 6605 = (267040390796809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6605 = 267040390796809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6605 = (2921:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6605
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6606) ≤ val WuPaper.ClassicalFourthData.Bq 6606
    have hp : val WuPaper.ClassicalFourthData.Bq 6606 = (267047930328671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6606 = 267047930328671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6606 = (7303:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6606
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6607) ≤ val WuPaper.ClassicalFourthData.Bq 6607
    have hp : val WuPaper.ClassicalFourthData.Bq 6607 = (267055466393794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6607 = 267055466393794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6607 = (14607:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6607
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_412
