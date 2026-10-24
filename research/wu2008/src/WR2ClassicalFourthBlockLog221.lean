import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints221
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_221 (j : Fin 16) (hj : 16*221+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*221+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*221+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3536) ≤ val WuPaper.ClassicalFourthData.Bq 3536
    have hp : val WuPaper.ClassicalFourthData.Bq 3536 = (219624540968853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3536 = 219624540968853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3536 = (721:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3536
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3537) ≤ val WuPaper.ClassicalFourthData.Bq 3537
    have hp : val WuPaper.ClassicalFourthData.Bq 3537 = (219651508621459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3537 = 219651508621459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3537 = (11537:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3537
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3538) ≤ val WuPaper.ClassicalFourthData.Bq 3538
    have hp : val WuPaper.ClassicalFourthData.Bq 3538 = (219678465496639:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3538 = 219678465496639 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3538 = (5769:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3538
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3539) ≤ val WuPaper.ClassicalFourthData.Bq 3539
    have hp : val WuPaper.ClassicalFourthData.Bq 3539 = (219705411598813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3539 = 219705411598813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3539 = (11539:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3539
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3540) ≤ val WuPaper.ClassicalFourthData.Bq 3540
    have hp : val WuPaper.ClassicalFourthData.Bq 3540 = (219732346932401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3540 = 219732346932401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3540 = (577:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3540
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3541) ≤ val WuPaper.ClassicalFourthData.Bq 3541
    have hp : val WuPaper.ClassicalFourthData.Bq 3541 = (219759271501818:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3541 = 219759271501818 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3541 = (11541:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3541
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3542) ≤ val WuPaper.ClassicalFourthData.Bq 3542
    have hp : val WuPaper.ClassicalFourthData.Bq 3542 = (219786185311480:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3542 = 219786185311480 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3542 = (5771:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3542
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3543) ≤ val WuPaper.ClassicalFourthData.Bq 3543
    have hp : val WuPaper.ClassicalFourthData.Bq 3543 = (219813088365799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3543 = 219813088365799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3543 = (11543:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3543
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3544) ≤ val WuPaper.ClassicalFourthData.Bq 3544
    have hp : val WuPaper.ClassicalFourthData.Bq 3544 = (219839980669185:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3544 = 219839980669185 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3544 = (1443:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3544
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3545) ≤ val WuPaper.ClassicalFourthData.Bq 3545
    have hp : val WuPaper.ClassicalFourthData.Bq 3545 = (219866862226045:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3545 = 219866862226045 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3545 = (2309:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3545
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3546) ≤ val WuPaper.ClassicalFourthData.Bq 3546
    have hp : val WuPaper.ClassicalFourthData.Bq 3546 = (219893733040786:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3546 = 219893733040786 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3546 = (5773:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3546
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3547) ≤ val WuPaper.ClassicalFourthData.Bq 3547
    have hp : val WuPaper.ClassicalFourthData.Bq 3547 = (219920593117811:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3547 = 219920593117811 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3547 = (11547:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3547
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3548) ≤ val WuPaper.ClassicalFourthData.Bq 3548
    have hp : val WuPaper.ClassicalFourthData.Bq 3548 = (219947442461522:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3548 = 219947442461522 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3548 = (2887:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3548
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3549) ≤ val WuPaper.ClassicalFourthData.Bq 3549
    have hp : val WuPaper.ClassicalFourthData.Bq 3549 = (219974281076318:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3549 = 219974281076318 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3549 = (11549:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3549
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3550) ≤ val WuPaper.ClassicalFourthData.Bq 3550
    have hp : val WuPaper.ClassicalFourthData.Bq 3550 = (220001108966595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3550 = 220001108966595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3550 = (231:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3550
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3551) ≤ val WuPaper.ClassicalFourthData.Bq 3551
    have hp : val WuPaper.ClassicalFourthData.Bq 3551 = (220027926136750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3551 = 220027926136750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3551 = (11551:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3551
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_221
