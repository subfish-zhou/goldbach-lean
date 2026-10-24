import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints345
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_345 (j : Fin 16) (hj : 16*345+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*345+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*345+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5520) ≤ val WuPaper.ClassicalFourthData.Bq 5520
    have hp : val WuPaper.ClassicalFourthData.Bq 5520 = (256538605823488:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5520 = 256538605823488 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5520 = (169:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5520
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5521) ≤ val WuPaper.ClassicalFourthData.Bq 5521
    have hp : val WuPaper.ClassicalFourthData.Bq 5521 = (256550706067205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5521 = 256550706067205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5521 = (13521:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5521
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5522) ≤ val WuPaper.ClassicalFourthData.Bq 5522
    have hp : val WuPaper.ClassicalFourthData.Bq 5522 = (256562801257933:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5522 = 256562801257933 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5522 = (6761:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5522
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5523) ≤ val WuPaper.ClassicalFourthData.Bq 5523
    have hp : val WuPaper.ClassicalFourthData.Bq 5523 = (256574891397478:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5523 = 256574891397478 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5523 = (13523:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5523
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5524) ≤ val WuPaper.ClassicalFourthData.Bq 5524
    have hp : val WuPaper.ClassicalFourthData.Bq 5524 = (256586976487646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5524 = 256586976487646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5524 = (3381:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5524
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5525) ≤ val WuPaper.ClassicalFourthData.Bq 5525
    have hp : val WuPaper.ClassicalFourthData.Bq 5525 = (256599056530242:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5525 = 256599056530242 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5525 = (541:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5525
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5526) ≤ val WuPaper.ClassicalFourthData.Bq 5526
    have hp : val WuPaper.ClassicalFourthData.Bq 5526 = (256611131527069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5526 = 256611131527069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5526 = (6763:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5526
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5527) ≤ val WuPaper.ClassicalFourthData.Bq 5527
    have hp : val WuPaper.ClassicalFourthData.Bq 5527 = (256623201479931:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5527 = 256623201479931 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5527 = (13527:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5527
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5528) ≤ val WuPaper.ClassicalFourthData.Bq 5528
    have hp : val WuPaper.ClassicalFourthData.Bq 5528 = (256635266390631:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5528 = 256635266390631 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5528 = (1691:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5528
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5529) ≤ val WuPaper.ClassicalFourthData.Bq 5529
    have hp : val WuPaper.ClassicalFourthData.Bq 5529 = (256647326260970:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5529 = 256647326260970 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5529 = (13529:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5529
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5530) ≤ val WuPaper.ClassicalFourthData.Bq 5530
    have hp : val WuPaper.ClassicalFourthData.Bq 5530 = (256659381092750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5530 = 256659381092750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5530 = (1353:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5530
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5531) ≤ val WuPaper.ClassicalFourthData.Bq 5531
    have hp : val WuPaper.ClassicalFourthData.Bq 5531 = (256671430887770:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5531 = 256671430887770 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5531 = (13531:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5531
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5532) ≤ val WuPaper.ClassicalFourthData.Bq 5532
    have hp : val WuPaper.ClassicalFourthData.Bq 5532 = (256683475647830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5532 = 256683475647830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5532 = (3383:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5532
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5533) ≤ val WuPaper.ClassicalFourthData.Bq 5533
    have hp : val WuPaper.ClassicalFourthData.Bq 5533 = (256695515374730:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5533 = 256695515374730 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5533 = (13533:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5533
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5534) ≤ val WuPaper.ClassicalFourthData.Bq 5534
    have hp : val WuPaper.ClassicalFourthData.Bq 5534 = (256707550070267:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5534 = 256707550070267 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5534 = (6767:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5534
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5535) ≤ val WuPaper.ClassicalFourthData.Bq 5535
    have hp : val WuPaper.ClassicalFourthData.Bq 5535 = (256719579736239:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5535 = 256719579736239 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5535 = (2707:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5535
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_345
