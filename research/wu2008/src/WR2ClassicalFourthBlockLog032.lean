import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints032
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_032 (j : Fin 16) (hj : 16*32+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*32+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*32+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 512) ≤ val WuPaper.ClassicalFourthData.Bq 512
    have hp : val WuPaper.ClassicalFourthData.Bq 512 = (56600635843923:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 512 = 56600635843923 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 512 = (266:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_512
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 513) ≤ val WuPaper.ClassicalFourthData.Bq 513
    have hp : val WuPaper.ClassicalFourthData.Bq 513 = (56698113344285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 513 = 56698113344285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 513 = (8513:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_513
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 514) ≤ val WuPaper.ClassicalFourthData.Bq 514
    have hp : val WuPaper.ClassicalFourthData.Bq 514 = (56795544879236:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 514 = 56795544879236 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 514 = (4257:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_514
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 515) ≤ val WuPaper.ClassicalFourthData.Bq 515
    have hp : val WuPaper.ClassicalFourthData.Bq 515 = (56892930475189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 515 = 56892930475189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 515 = (1703:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_515
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 516) ≤ val WuPaper.ClassicalFourthData.Bq 516
    have hp : val WuPaper.ClassicalFourthData.Bq 516 = (56990270158537:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 516 = 56990270158537 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 516 = (2129:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_516
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 517) ≤ val WuPaper.ClassicalFourthData.Bq 517
    have hp : val WuPaper.ClassicalFourthData.Bq 517 = (57087563955655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 517 = 57087563955655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 517 = (8517:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_517
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 518) ≤ val WuPaper.ClassicalFourthData.Bq 518
    have hp : val WuPaper.ClassicalFourthData.Bq 518 = (57184811892896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 518 = 57184811892896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 518 = (4259:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_518
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 519) ≤ val WuPaper.ClassicalFourthData.Bq 519
    have hp : val WuPaper.ClassicalFourthData.Bq 519 = (57282013996597:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 519 = 57282013996597 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 519 = (8519:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_519
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 520) ≤ val WuPaper.ClassicalFourthData.Bq 520
    have hp : val WuPaper.ClassicalFourthData.Bq 520 = (57379170293075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 520 = 57379170293075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 520 = (213:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_520
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 521) ≤ val WuPaper.ClassicalFourthData.Bq 521
    have hp : val WuPaper.ClassicalFourthData.Bq 521 = (57476280808627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 521 = 57476280808627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 521 = (8521:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_521
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 522) ≤ val WuPaper.ClassicalFourthData.Bq 522
    have hp : val WuPaper.ClassicalFourthData.Bq 522 = (57573345569532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 522 = 57573345569532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 522 = (4261:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_522
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 523) ≤ val WuPaper.ClassicalFourthData.Bq 523
    have hp : val WuPaper.ClassicalFourthData.Bq 523 = (57670364602049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 523 = 57670364602049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 523 = (8523:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_523
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 524) ≤ val WuPaper.ClassicalFourthData.Bq 524
    have hp : val WuPaper.ClassicalFourthData.Bq 524 = (57767337932419:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 524 = 57767337932419 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 524 = (2131:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_524
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 525) ≤ val WuPaper.ClassicalFourthData.Bq 525
    have hp : val WuPaper.ClassicalFourthData.Bq 525 = (57864265586862:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 525 = 57864265586862 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 525 = (341:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_525
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 526) ≤ val WuPaper.ClassicalFourthData.Bq 526
    have hp : val WuPaper.ClassicalFourthData.Bq 526 = (57961147591582:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 526 = 57961147591582 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 526 = (4263:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_526
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 527) ≤ val WuPaper.ClassicalFourthData.Bq 527
    have hp : val WuPaper.ClassicalFourthData.Bq 527 = (58057983972760:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 527 = 58057983972760 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 527 = (8527:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_527
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_032
