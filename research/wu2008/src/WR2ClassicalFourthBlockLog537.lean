import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints537
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_537 (j : Fin 16) (hj : 16*537+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*537+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*537+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8592) ≤ val WuPaper.ClassicalFourthData.Bq 8592
    have hp : val WuPaper.ClassicalFourthData.Bq 8592 = (276462712286289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8592 = 276462712286289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8592 = (1037:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8592
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8593) ≤ val WuPaper.ClassicalFourthData.Bq 8593
    have hp : val WuPaper.ClassicalFourthData.Bq 8593 = (276465194458435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8593 = 276465194458435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8593 = (16593:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8593
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8594) ≤ val WuPaper.ClassicalFourthData.Bq 8594
    have hp : val WuPaper.ClassicalFourthData.Bq 8594 = (276467674811392:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8594 = 276467674811392 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8594 = (8297:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8594
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8595) ≤ val WuPaper.ClassicalFourthData.Bq 8595
    have hp : val WuPaper.ClassicalFourthData.Bq 8595 = (276470153345731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8595 = 276470153345731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8595 = (3319:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8595
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8596) ≤ val WuPaper.ClassicalFourthData.Bq 8596
    have hp : val WuPaper.ClassicalFourthData.Bq 8596 = (276472630062020:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8596 = 276472630062020 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8596 = (4149:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8596
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8597) ≤ val WuPaper.ClassicalFourthData.Bq 8597
    have hp : val WuPaper.ClassicalFourthData.Bq 8597 = (276475104960830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8597 = 276475104960830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8597 = (16597:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8597
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8598) ≤ val WuPaper.ClassicalFourthData.Bq 8598
    have hp : val WuPaper.ClassicalFourthData.Bq 8598 = (276477578042731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8598 = 276477578042731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8598 = (8299:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8598
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8599) ≤ val WuPaper.ClassicalFourthData.Bq 8599
    have hp : val WuPaper.ClassicalFourthData.Bq 8599 = (276480049308292:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8599 = 276480049308292 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8599 = (16599:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8599
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8600) ≤ val WuPaper.ClassicalFourthData.Bq 8600
    have hp : val WuPaper.ClassicalFourthData.Bq 8600 = (276482518758082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8600 = 276482518758082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8600 = (83:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8600
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8601) ≤ val WuPaper.ClassicalFourthData.Bq 8601
    have hp : val WuPaper.ClassicalFourthData.Bq 8601 = (276484986392670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8601 = 276484986392670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8601 = (16601:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8601
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8602) ≤ val WuPaper.ClassicalFourthData.Bq 8602
    have hp : val WuPaper.ClassicalFourthData.Bq 8602 = (276487452212626:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8602 = 276487452212626 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8602 = (8301:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8602
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8603) ≤ val WuPaper.ClassicalFourthData.Bq 8603
    have hp : val WuPaper.ClassicalFourthData.Bq 8603 = (276489916218517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8603 = 276489916218517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8603 = (16603:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8603
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8604) ≤ val WuPaper.ClassicalFourthData.Bq 8604
    have hp : val WuPaper.ClassicalFourthData.Bq 8604 = (276492378410913:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8604 = 276492378410913 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8604 = (4151:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8604
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8605) ≤ val WuPaper.ClassicalFourthData.Bq 8605
    have hp : val WuPaper.ClassicalFourthData.Bq 8605 = (276494838790382:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8605 = 276494838790382 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8605 = (3321:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8605
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8606) ≤ val WuPaper.ClassicalFourthData.Bq 8606
    have hp : val WuPaper.ClassicalFourthData.Bq 8606 = (276497297357491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8606 = 276497297357491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8606 = (8303:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8606
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8607) ≤ val WuPaper.ClassicalFourthData.Bq 8607
    have hp : val WuPaper.ClassicalFourthData.Bq 8607 = (276499754112809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8607 = 276499754112809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8607 = (16607:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8607
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_537
