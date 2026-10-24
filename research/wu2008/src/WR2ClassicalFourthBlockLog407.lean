import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints407
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_407 (j : Fin 16) (hj : 16*407+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*407+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*407+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6512) ≤ val WuPaper.ClassicalFourthData.Bq 6512
    have hp : val WuPaper.ClassicalFourthData.Bq 6512 = (266323897635732:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6512 = 266323897635732 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6512 = (907:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6512
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6513) ≤ val WuPaper.ClassicalFourthData.Bq 6513
    have hp : val WuPaper.ClassicalFourthData.Bq 6513 = (266331764755427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6513 = 266331764755427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6513 = (14513:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6513
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6514) ≤ val WuPaper.ClassicalFourthData.Bq 6514
    have hp : val WuPaper.ClassicalFourthData.Bq 6514 = (266339628297489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6514 = 266339628297489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6514 = (7257:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6514
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6515) ≤ val WuPaper.ClassicalFourthData.Bq 6515
    have hp : val WuPaper.ClassicalFourthData.Bq 6515 = (266347488263134:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6515 = 266347488263134 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6515 = (2903:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6515
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6516) ≤ val WuPaper.ClassicalFourthData.Bq 6516
    have hp : val WuPaper.ClassicalFourthData.Bq 6516 = (266355344653573:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6516 = 266355344653573 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6516 = (3629:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6516
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6517) ≤ val WuPaper.ClassicalFourthData.Bq 6517
    have hp : val WuPaper.ClassicalFourthData.Bq 6517 = (266363197470021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6517 = 266363197470021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6517 = (14517:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6517
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6518) ≤ val WuPaper.ClassicalFourthData.Bq 6518
    have hp : val WuPaper.ClassicalFourthData.Bq 6518 = (266371046713690:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6518 = 266371046713690 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6518 = (7259:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6518
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6519) ≤ val WuPaper.ClassicalFourthData.Bq 6519
    have hp : val WuPaper.ClassicalFourthData.Bq 6519 = (266378892385790:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6519 = 266378892385790 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6519 = (14519:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6519
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6520) ≤ val WuPaper.ClassicalFourthData.Bq 6520
    have hp : val WuPaper.ClassicalFourthData.Bq 6520 = (266386734487534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6520 = 266386734487534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6520 = (363:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6520
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6521) ≤ val WuPaper.ClassicalFourthData.Bq 6521
    have hp : val WuPaper.ClassicalFourthData.Bq 6521 = (266394573020132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6521 = 266394573020132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6521 = (14521:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6521
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6522) ≤ val WuPaper.ClassicalFourthData.Bq 6522
    have hp : val WuPaper.ClassicalFourthData.Bq 6522 = (266402407984796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6522 = 266402407984796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6522 = (7261:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6522
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6523) ≤ val WuPaper.ClassicalFourthData.Bq 6523
    have hp : val WuPaper.ClassicalFourthData.Bq 6523 = (266410239382734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6523 = 266410239382734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6523 = (14523:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6523
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6524) ≤ val WuPaper.ClassicalFourthData.Bq 6524
    have hp : val WuPaper.ClassicalFourthData.Bq 6524 = (266418067215156:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6524 = 266418067215156 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6524 = (3631:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6524
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6525) ≤ val WuPaper.ClassicalFourthData.Bq 6525
    have hp : val WuPaper.ClassicalFourthData.Bq 6525 = (266425891483272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6525 = 266425891483272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6525 = (581:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6525
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6526) ≤ val WuPaper.ClassicalFourthData.Bq 6526
    have hp : val WuPaper.ClassicalFourthData.Bq 6526 = (266433712188289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6526 = 266433712188289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6526 = (7263:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6526
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6527) ≤ val WuPaper.ClassicalFourthData.Bq 6527
    have hp : val WuPaper.ClassicalFourthData.Bq 6527 = (266441529331417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6527 = 266441529331417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6527 = (14527:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6527
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_407
