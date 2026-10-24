import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints528
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_528 (j : Fin 16) (hj : 16*528+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*528+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*528+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8448) ≤ val WuPaper.ClassicalFourthData.Bq 8448
    have hp : val WuPaper.ClassicalFourthData.Bq 8448 = (276085993755466:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8448 = 276085993755466 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8448 = (514:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8448
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8449) ≤ val WuPaper.ClassicalFourthData.Bq 8449
    have hp : val WuPaper.ClassicalFourthData.Bq 8449 = (276088743944581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8449 = 276088743944581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8449 = (16449:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8449
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8450) ≤ val WuPaper.ClassicalFourthData.Bq 8450
    have hp : val WuPaper.ClassicalFourthData.Bq 8450 = (276091492230318:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8450 = 276091492230318 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8450 = (329:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8450
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8451) ≤ val WuPaper.ClassicalFourthData.Bq 8451
    have hp : val WuPaper.ClassicalFourthData.Bq 8451 = (276094238613277:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8451 = 276094238613277 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8451 = (16451:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8451
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8452) ≤ val WuPaper.ClassicalFourthData.Bq 8452
    have hp : val WuPaper.ClassicalFourthData.Bq 8452 = (276096983094056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8452 = 276096983094056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8452 = (4113:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8452
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8453) ≤ val WuPaper.ClassicalFourthData.Bq 8453
    have hp : val WuPaper.ClassicalFourthData.Bq 8453 = (276099725673255:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8453 = 276099725673255 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8453 = (16453:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8453
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8454) ≤ val WuPaper.ClassicalFourthData.Bq 8454
    have hp : val WuPaper.ClassicalFourthData.Bq 8454 = (276102466351471:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8454 = 276102466351471 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8454 = (8227:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8454
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8455) ≤ val WuPaper.ClassicalFourthData.Bq 8455
    have hp : val WuPaper.ClassicalFourthData.Bq 8455 = (276105205129304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8455 = 276105205129304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8455 = (3291:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8455
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8456) ≤ val WuPaper.ClassicalFourthData.Bq 8456
    have hp : val WuPaper.ClassicalFourthData.Bq 8456 = (276107942007350:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8456 = 276107942007350 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8456 = (2057:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8456
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8457) ≤ val WuPaper.ClassicalFourthData.Bq 8457
    have hp : val WuPaper.ClassicalFourthData.Bq 8457 = (276110676986209:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8457 = 276110676986209 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8457 = (16457:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8457
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8458) ≤ val WuPaper.ClassicalFourthData.Bq 8458
    have hp : val WuPaper.ClassicalFourthData.Bq 8458 = (276113410066477:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8458 = 276113410066477 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8458 = (8229:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8458
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8459) ≤ val WuPaper.ClassicalFourthData.Bq 8459
    have hp : val WuPaper.ClassicalFourthData.Bq 8459 = (276116141248753:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8459 = 276116141248753 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8459 = (16459:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8459
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8460) ≤ val WuPaper.ClassicalFourthData.Bq 8460
    have hp : val WuPaper.ClassicalFourthData.Bq 8460 = (276118870533633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8460 = 276118870533633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8460 = (823:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8460
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8461) ≤ val WuPaper.ClassicalFourthData.Bq 8461
    have hp : val WuPaper.ClassicalFourthData.Bq 8461 = (276121597921715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8461 = 276121597921715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8461 = (16461:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8461
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8462) ≤ val WuPaper.ClassicalFourthData.Bq 8462
    have hp : val WuPaper.ClassicalFourthData.Bq 8462 = (276124323413595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8462 = 276124323413595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8462 = (8231:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8462
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8463) ≤ val WuPaper.ClassicalFourthData.Bq 8463
    have hp : val WuPaper.ClassicalFourthData.Bq 8463 = (276127047009870:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8463 = 276127047009870 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8463 = (16463:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8463
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_528
