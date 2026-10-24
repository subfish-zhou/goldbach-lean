import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints590
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_590 (j : Fin 16) (hj : 16*590+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*590+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*590+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9440) ≤ val WuPaper.ClassicalFourthData.Bq 9440
    have hp : val WuPaper.ClassicalFourthData.Bq 9440 = (277968113305850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9440 = 277968113305850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9440 = (109:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9440
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9441) ≤ val WuPaper.ClassicalFourthData.Bq 9441
    have hp : val WuPaper.ClassicalFourthData.Bq 9441 = (277969239380214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9441 = 277969239380214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9441 = (17441:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9441
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9442) ≤ val WuPaper.ClassicalFourthData.Bq 9442
    have hp : val WuPaper.ClassicalFourthData.Bq 9442 = (277970364056050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9442 = 277970364056050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9442 = (8721:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9442
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9443) ≤ val WuPaper.ClassicalFourthData.Bq 9443
    have hp : val WuPaper.ClassicalFourthData.Bq 9443 = (277971487333787:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9443 = 277971487333787 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9443 = (17443:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9443
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9444) ≤ val WuPaper.ClassicalFourthData.Bq 9444
    have hp : val WuPaper.ClassicalFourthData.Bq 9444 = (277972609213855:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9444 = 277972609213855 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9444 = (4361:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9444
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9445) ≤ val WuPaper.ClassicalFourthData.Bq 9445
    have hp : val WuPaper.ClassicalFourthData.Bq 9445 = (277973729696682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9445 = 277973729696682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9445 = (3489:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9445
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9446) ≤ val WuPaper.ClassicalFourthData.Bq 9446
    have hp : val WuPaper.ClassicalFourthData.Bq 9446 = (277974848782698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9446 = 277974848782698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9446 = (8723:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9446
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9447) ≤ val WuPaper.ClassicalFourthData.Bq 9447
    have hp : val WuPaper.ClassicalFourthData.Bq 9447 = (277975966472331:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9447 = 277975966472331 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9447 = (17447:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9447
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9448) ≤ val WuPaper.ClassicalFourthData.Bq 9448
    have hp : val WuPaper.ClassicalFourthData.Bq 9448 = (277977082766010:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9448 = 277977082766010 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9448 = (2181:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9448
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9449) ≤ val WuPaper.ClassicalFourthData.Bq 9449
    have hp : val WuPaper.ClassicalFourthData.Bq 9449 = (277978197664164:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9449 = 277978197664164 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9449 = (17449:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9449
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9450) ≤ val WuPaper.ClassicalFourthData.Bq 9450
    have hp : val WuPaper.ClassicalFourthData.Bq 9450 = (277979311167221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9450 = 277979311167221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9450 = (349:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9450
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9451) ≤ val WuPaper.ClassicalFourthData.Bq 9451
    have hp : val WuPaper.ClassicalFourthData.Bq 9451 = (277980423275609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9451 = 277980423275609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9451 = (17451:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9451
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9452) ≤ val WuPaper.ClassicalFourthData.Bq 9452
    have hp : val WuPaper.ClassicalFourthData.Bq 9452 = (277981533989757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9452 = 277981533989757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9452 = (4363:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9452
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9453) ≤ val WuPaper.ClassicalFourthData.Bq 9453
    have hp : val WuPaper.ClassicalFourthData.Bq 9453 = (277982643310092:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9453 = 277982643310092 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9453 = (17453:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9453
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9454) ≤ val WuPaper.ClassicalFourthData.Bq 9454
    have hp : val WuPaper.ClassicalFourthData.Bq 9454 = (277983751237042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9454 = 277983751237042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9454 = (8727:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9454
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9455) ≤ val WuPaper.ClassicalFourthData.Bq 9455
    have hp : val WuPaper.ClassicalFourthData.Bq 9455 = (277984857771035:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9455 = 277984857771035 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9455 = (3491:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9455
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_590
