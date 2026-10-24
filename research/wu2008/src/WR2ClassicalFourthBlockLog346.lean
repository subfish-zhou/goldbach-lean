import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints346
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_346 (j : Fin 16) (hj : 16*346+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*346+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*346+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5536) ≤ val WuPaper.ClassicalFourthData.Bq 5536
    have hp : val WuPaper.ClassicalFourthData.Bq 5536 = (256731604374441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5536 = 256731604374441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5536 = (423:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5536
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5537) ≤ val WuPaper.ClassicalFourthData.Bq 5537
    have hp : val WuPaper.ClassicalFourthData.Bq 5537 = (256743623986671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5537 = 256743623986671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5537 = (13537:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5537
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5538) ≤ val WuPaper.ClassicalFourthData.Bq 5538
    have hp : val WuPaper.ClassicalFourthData.Bq 5538 = (256755638574722:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5538 = 256755638574722 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5538 = (6769:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5538
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5539) ≤ val WuPaper.ClassicalFourthData.Bq 5539
    have hp : val WuPaper.ClassicalFourthData.Bq 5539 = (256767648140390:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5539 = 256767648140390 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5539 = (13539:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5539
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5540) ≤ val WuPaper.ClassicalFourthData.Bq 5540
    have hp : val WuPaper.ClassicalFourthData.Bq 5540 = (256779652685468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5540 = 256779652685468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5540 = (677:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5540
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5541) ≤ val WuPaper.ClassicalFourthData.Bq 5541
    have hp : val WuPaper.ClassicalFourthData.Bq 5541 = (256791652211749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5541 = 256791652211749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5541 = (13541:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5541
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5542) ≤ val WuPaper.ClassicalFourthData.Bq 5542
    have hp : val WuPaper.ClassicalFourthData.Bq 5542 = (256803646721025:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5542 = 256803646721025 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5542 = (6771:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5542
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5543) ≤ val WuPaper.ClassicalFourthData.Bq 5543
    have hp : val WuPaper.ClassicalFourthData.Bq 5543 = (256815636215087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5543 = 256815636215087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5543 = (13543:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5543
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5544) ≤ val WuPaper.ClassicalFourthData.Bq 5544
    have hp : val WuPaper.ClassicalFourthData.Bq 5544 = (256827620695726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5544 = 256827620695726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5544 = (1693:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5544
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5545) ≤ val WuPaper.ClassicalFourthData.Bq 5545
    have hp : val WuPaper.ClassicalFourthData.Bq 5545 = (256839600164733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5545 = 256839600164733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5545 = (2709:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5545
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5546) ≤ val WuPaper.ClassicalFourthData.Bq 5546
    have hp : val WuPaper.ClassicalFourthData.Bq 5546 = (256851574623895:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5546 = 256851574623895 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5546 = (6773:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5546
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5547) ≤ val WuPaper.ClassicalFourthData.Bq 5547
    have hp : val WuPaper.ClassicalFourthData.Bq 5547 = (256863544075001:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5547 = 256863544075001 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5547 = (13547:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5547
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5548) ≤ val WuPaper.ClassicalFourthData.Bq 5548
    have hp : val WuPaper.ClassicalFourthData.Bq 5548 = (256875508519840:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5548 = 256875508519840 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5548 = (3387:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5548
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5549) ≤ val WuPaper.ClassicalFourthData.Bq 5549
    have hp : val WuPaper.ClassicalFourthData.Bq 5549 = (256887467960198:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5549 = 256887467960198 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5549 = (13549:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5549
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5550) ≤ val WuPaper.ClassicalFourthData.Bq 5550
    have hp : val WuPaper.ClassicalFourthData.Bq 5550 = (256899422397861:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5550 = 256899422397861 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5550 = (271:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5550
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5551) ≤ val WuPaper.ClassicalFourthData.Bq 5551
    have hp : val WuPaper.ClassicalFourthData.Bq 5551 = (256911371834615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5551 = 256911371834615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5551 = (13551:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5551
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_346
