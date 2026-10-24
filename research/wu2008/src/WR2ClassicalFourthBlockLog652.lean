import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints652
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_652 (j : Fin 16) (hj : 16*652+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*652+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*652+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10432) ≤ val WuPaper.ClassicalFourthData.Bq 10432
    have hp : val WuPaper.ClassicalFourthData.Bq 10432 = (278462153295056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10432 = 278462153295056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10432 = (576:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10432
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10433) ≤ val WuPaper.ClassicalFourthData.Bq 10433
    have hp : val WuPaper.ClassicalFourthData.Bq 10433 = (278462082232745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10433 = 278462082232745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10433 = (18433:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10433
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10434) ≤ val WuPaper.ClassicalFourthData.Bq 10434
    have hp : val WuPaper.ClassicalFourthData.Bq 10434 = (278462010136481:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10434 = 278462010136481 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10434 = (9217:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10434
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10435) ≤ val WuPaper.ClassicalFourthData.Bq 10435
    have hp : val WuPaper.ClassicalFourthData.Bq 10435 = (278461937006577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10435 = 278461937006577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10435 = (3687:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10435
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10436) ≤ val WuPaper.ClassicalFourthData.Bq 10436
    have hp : val WuPaper.ClassicalFourthData.Bq 10436 = (278461862843345:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10436 = 278461862843345 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10436 = (4609:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10436
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10437) ≤ val WuPaper.ClassicalFourthData.Bq 10437
    have hp : val WuPaper.ClassicalFourthData.Bq 10437 = (278461787647097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10437 = 278461787647097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10437 = (18437:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10437
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10438) ≤ val WuPaper.ClassicalFourthData.Bq 10438
    have hp : val WuPaper.ClassicalFourthData.Bq 10438 = (278461711418146:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10438 = 278461711418146 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10438 = (9219:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10438
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10439) ≤ val WuPaper.ClassicalFourthData.Bq 10439
    have hp : val WuPaper.ClassicalFourthData.Bq 10439 = (278461634156805:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10439 = 278461634156805 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10439 = (18439:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10439
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10440) ≤ val WuPaper.ClassicalFourthData.Bq 10440
    have hp : val WuPaper.ClassicalFourthData.Bq 10440 = (278461555863384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10440 = 278461555863384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10440 = (461:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10440
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10441) ≤ val WuPaper.ClassicalFourthData.Bq 10441
    have hp : val WuPaper.ClassicalFourthData.Bq 10441 = (278461476538197:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10441 = 278461476538197 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10441 = (18441:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10441
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10442) ≤ val WuPaper.ClassicalFourthData.Bq 10442
    have hp : val WuPaper.ClassicalFourthData.Bq 10442 = (278461396181554:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10442 = 278461396181554 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10442 = (9221:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10442
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10443) ≤ val WuPaper.ClassicalFourthData.Bq 10443
    have hp : val WuPaper.ClassicalFourthData.Bq 10443 = (278461314793769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10443 = 278461314793769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10443 = (18443:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10443
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10444) ≤ val WuPaper.ClassicalFourthData.Bq 10444
    have hp : val WuPaper.ClassicalFourthData.Bq 10444 = (278461232375152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10444 = 278461232375152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10444 = (4611:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10444
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10445) ≤ val WuPaper.ClassicalFourthData.Bq 10445
    have hp : val WuPaper.ClassicalFourthData.Bq 10445 = (278461148926015:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10445 = 278461148926015 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10445 = (3689:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10445
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10446) ≤ val WuPaper.ClassicalFourthData.Bq 10446
    have hp : val WuPaper.ClassicalFourthData.Bq 10446 = (278461064446670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10446 = 278461064446670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10446 = (9223:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10446
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10447) ≤ val WuPaper.ClassicalFourthData.Bq 10447
    have hp : val WuPaper.ClassicalFourthData.Bq 10447 = (278460978937428:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10447 = 278460978937428 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10447 = (18447:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_652
