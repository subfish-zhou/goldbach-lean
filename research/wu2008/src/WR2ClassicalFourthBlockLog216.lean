import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints216
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_216 (j : Fin 16) (hj : 16*216+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*216+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*216+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3456) ≤ val WuPaper.ClassicalFourthData.Bq 3456
    have hp : val WuPaper.ClassicalFourthData.Bq 3456 = (217431814337780:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3456 = 217431814337780 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3456 = (358:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3456
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3457) ≤ val WuPaper.ClassicalFourthData.Bq 3457
    have hp : val WuPaper.ClassicalFourthData.Bq 3457 = (217459658703594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3457 = 217459658703594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3457 = (11457:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3457
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3458) ≤ val WuPaper.ClassicalFourthData.Bq 3458
    have hp : val WuPaper.ClassicalFourthData.Bq 3458 = (217487491931136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3458 = 217487491931136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3458 = (5729:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3458
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3459) ≤ val WuPaper.ClassicalFourthData.Bq 3459
    have hp : val WuPaper.ClassicalFourthData.Bq 3459 = (217515314025006:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3459 = 217515314025006 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3459 = (11459:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3459
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3460) ≤ val WuPaper.ClassicalFourthData.Bq 3460
    have hp : val WuPaper.ClassicalFourthData.Bq 3460 = (217543124989801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3460 = 217543124989801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3460 = (573:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3460
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3461) ≤ val WuPaper.ClassicalFourthData.Bq 3461
    have hp : val WuPaper.ClassicalFourthData.Bq 3461 = (217570924830115:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3461 = 217570924830115 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3461 = (11461:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3461
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3462) ≤ val WuPaper.ClassicalFourthData.Bq 3462
    have hp : val WuPaper.ClassicalFourthData.Bq 3462 = (217598713550542:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3462 = 217598713550542 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3462 = (5731:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3462
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3463) ≤ val WuPaper.ClassicalFourthData.Bq 3463
    have hp : val WuPaper.ClassicalFourthData.Bq 3463 = (217626491155670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3463 = 217626491155670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3463 = (11463:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3463
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3464) ≤ val WuPaper.ClassicalFourthData.Bq 3464
    have hp : val WuPaper.ClassicalFourthData.Bq 3464 = (217654257650088:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3464 = 217654257650088 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3464 = (1433:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3464
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3465) ≤ val WuPaper.ClassicalFourthData.Bq 3465
    have hp : val WuPaper.ClassicalFourthData.Bq 3465 = (217682013038383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3465 = 217682013038383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3465 = (2293:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3465
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3466) ≤ val WuPaper.ClassicalFourthData.Bq 3466
    have hp : val WuPaper.ClassicalFourthData.Bq 3466 = (217709757325136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3466 = 217709757325136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3466 = (5733:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3466
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3467) ≤ val WuPaper.ClassicalFourthData.Bq 3467
    have hp : val WuPaper.ClassicalFourthData.Bq 3467 = (217737490514930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3467 = 217737490514930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3467 = (11467:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3467
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3468) ≤ val WuPaper.ClassicalFourthData.Bq 3468
    have hp : val WuPaper.ClassicalFourthData.Bq 3468 = (217765212612343:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3468 = 217765212612343 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3468 = (2867:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3468
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3469) ≤ val WuPaper.ClassicalFourthData.Bq 3469
    have hp : val WuPaper.ClassicalFourthData.Bq 3469 = (217792923621951:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3469 = 217792923621951 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3469 = (11469:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3469
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3470) ≤ val WuPaper.ClassicalFourthData.Bq 3470
    have hp : val WuPaper.ClassicalFourthData.Bq 3470 = (217820623548330:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3470 = 217820623548330 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3470 = (1147:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3470
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3471) ≤ val WuPaper.ClassicalFourthData.Bq 3471
    have hp : val WuPaper.ClassicalFourthData.Bq 3471 = (217848312396051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3471 = 217848312396051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3471 = (11471:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3471
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_216
