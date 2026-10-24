import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints654
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_654 (j : Fin 16) (hj : 16*654+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*654+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*654+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10464) ≤ val WuPaper.ClassicalFourthData.Bq 10464
    have hp : val WuPaper.ClassicalFourthData.Bq 10464 = (278459368007364:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10464 = 278459368007364 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10464 = (577:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10464
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10465) ≤ val WuPaper.ClassicalFourthData.Bq 10465
    have hp : val WuPaper.ClassicalFourthData.Bq 10465 = (278459264013117:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10465 = 278459264013117 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10465 = (3693:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10465
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10466) ≤ val WuPaper.ClassicalFourthData.Bq 10466
    have hp : val WuPaper.ClassicalFourthData.Bq 10466 = (278459158994871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10466 = 278459158994871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10466 = (9233:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10466
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10467) ≤ val WuPaper.ClassicalFourthData.Bq 10467
    have hp : val WuPaper.ClassicalFourthData.Bq 10467 = (278459052952937:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10467 = 278459052952937 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10467 = (18467:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10467
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10468) ≤ val WuPaper.ClassicalFourthData.Bq 10468
    have hp : val WuPaper.ClassicalFourthData.Bq 10468 = (278458945887622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10468 = 278458945887622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10468 = (4617:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10468
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10469) ≤ val WuPaper.ClassicalFourthData.Bq 10469
    have hp : val WuPaper.ClassicalFourthData.Bq 10469 = (278458837799237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10469 = 278458837799237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10469 = (18469:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10469
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10470) ≤ val WuPaper.ClassicalFourthData.Bq 10470
    have hp : val WuPaper.ClassicalFourthData.Bq 10470 = (278458728688091:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10470 = 278458728688091 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10470 = (1847:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10470
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10471) ≤ val WuPaper.ClassicalFourthData.Bq 10471
    have hp : val WuPaper.ClassicalFourthData.Bq 10471 = (278458618554492:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10471 = 278458618554492 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10471 = (18471:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10471
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10472) ≤ val WuPaper.ClassicalFourthData.Bq 10472
    have hp : val WuPaper.ClassicalFourthData.Bq 10472 = (278458507398750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10472 = 278458507398750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10472 = (2309:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10472
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10473) ≤ val WuPaper.ClassicalFourthData.Bq 10473
    have hp : val WuPaper.ClassicalFourthData.Bq 10473 = (278458395221174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10473 = 278458395221174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10473 = (18473:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10473
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10474) ≤ val WuPaper.ClassicalFourthData.Bq 10474
    have hp : val WuPaper.ClassicalFourthData.Bq 10474 = (278458282022072:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10474 = 278458282022072 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10474 = (9237:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10474
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10475) ≤ val WuPaper.ClassicalFourthData.Bq 10475
    have hp : val WuPaper.ClassicalFourthData.Bq 10475 = (278458167801754:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10475 = 278458167801754 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10475 = (739:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10475
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10476) ≤ val WuPaper.ClassicalFourthData.Bq 10476
    have hp : val WuPaper.ClassicalFourthData.Bq 10476 = (278458052560527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10476 = 278458052560527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10476 = (4619:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10476
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10477) ≤ val WuPaper.ClassicalFourthData.Bq 10477
    have hp : val WuPaper.ClassicalFourthData.Bq 10477 = (278457936298700:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10477 = 278457936298700 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10477 = (18477:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10477
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10478) ≤ val WuPaper.ClassicalFourthData.Bq 10478
    have hp : val WuPaper.ClassicalFourthData.Bq 10478 = (278457819016582:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10478 = 278457819016582 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10478 = (9239:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10478
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10479) ≤ val WuPaper.ClassicalFourthData.Bq 10479
    have hp : val WuPaper.ClassicalFourthData.Bq 10479 = (278457700714480:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10479 = 278457700714480 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10479 = (18479:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10479
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_654
