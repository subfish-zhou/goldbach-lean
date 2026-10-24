import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints028
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_028 (j : Fin 16) (hj : 16*28+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*28+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*28+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 448) ≤ val WuPaper.ClassicalFourthData.Bq 448
    have hp : val WuPaper.ClassicalFourthData.Bq 448 = (50265244236928:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 448 = 50265244236928 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 448 = (264:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_448
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 449) ≤ val WuPaper.ClassicalFourthData.Bq 449
    have hp : val WuPaper.ClassicalFourthData.Bq 449 = (50365719353303:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 449 = 50365719353303 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 449 = (8449:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_449
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 450) ≤ val WuPaper.ClassicalFourthData.Bq 450
    have hp : val WuPaper.ClassicalFourthData.Bq 450 = (50466146773140:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 450 = 50466146773140 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 450 = (169:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_450
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 451) ≤ val WuPaper.ClassicalFourthData.Bq 451
    have hp : val WuPaper.ClassicalFourthData.Bq 451 = (50566526524117:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 451 = 50566526524117 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 451 = (8451:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_451
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 452) ≤ val WuPaper.ClassicalFourthData.Bq 452
    have hp : val WuPaper.ClassicalFourthData.Bq 452 = (50666858633890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 452 = 50666858633890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 452 = (2113:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_452
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 453) ≤ val WuPaper.ClassicalFourthData.Bq 453
    have hp : val WuPaper.ClassicalFourthData.Bq 453 = (50767143130096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 453 = 50767143130096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 453 = (8453:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_453
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 454) ≤ val WuPaper.ClassicalFourthData.Bq 454
    have hp : val WuPaper.ClassicalFourthData.Bq 454 = (50867380040353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 454 = 50867380040353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 454 = (4227:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_454
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 455) ≤ val WuPaper.ClassicalFourthData.Bq 455
    have hp : val WuPaper.ClassicalFourthData.Bq 455 = (50967569392257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 455 = 50967569392257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 455 = (1691:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_455
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 456) ≤ val WuPaper.ClassicalFourthData.Bq 456
    have hp : val WuPaper.ClassicalFourthData.Bq 456 = (51067711213384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 456 = 51067711213384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 456 = (1057:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_456
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 457) ≤ val WuPaper.ClassicalFourthData.Bq 457
    have hp : val WuPaper.ClassicalFourthData.Bq 457 = (51167805531290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 457 = 51167805531290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 457 = (8457:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_457
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 458) ≤ val WuPaper.ClassicalFourthData.Bq 458
    have hp : val WuPaper.ClassicalFourthData.Bq 458 = (51267852373510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 458 = 51267852373510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 458 = (4229:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_458
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 459) ≤ val WuPaper.ClassicalFourthData.Bq 459
    have hp : val WuPaper.ClassicalFourthData.Bq 459 = (51367851767561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 459 = 51367851767561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 459 = (8459:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_459
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 460) ≤ val WuPaper.ClassicalFourthData.Bq 460
    have hp : val WuPaper.ClassicalFourthData.Bq 460 = (51467803740938:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 460 = 51467803740938 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 460 = (423:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_460
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 461) ≤ val WuPaper.ClassicalFourthData.Bq 461
    have hp : val WuPaper.ClassicalFourthData.Bq 461 = (51567708321115:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 461 = 51567708321115 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 461 = (8461:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_461
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 462) ≤ val WuPaper.ClassicalFourthData.Bq 462
    have hp : val WuPaper.ClassicalFourthData.Bq 462 = (51667565535548:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 462 = 51667565535548 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 462 = (4231:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_462
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 463) ≤ val WuPaper.ClassicalFourthData.Bq 463
    have hp : val WuPaper.ClassicalFourthData.Bq 463 = (51767375411671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 463 = 51767375411671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 463 = (8463:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_463
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_028
