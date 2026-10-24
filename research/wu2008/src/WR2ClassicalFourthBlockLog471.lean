import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints471
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_471 (j : Fin 16) (hj : 16*471+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*471+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*471+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7536) ≤ val WuPaper.ClassicalFourthData.Bq 7536
    have hp : val WuPaper.ClassicalFourthData.Bq 7536 = (272702940119369:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7536 = 272702940119369 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7536 = (971:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7536
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7537) ≤ val WuPaper.ClassicalFourthData.Bq 7537
    have hp : val WuPaper.ClassicalFourthData.Bq 7537 = (272707704402701:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7537 = 272707704402701 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7537 = (15537:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7537
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7538) ≤ val WuPaper.ClassicalFourthData.Bq 7538
    have hp : val WuPaper.ClassicalFourthData.Bq 7538 = (272712466138689:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7538 = 272712466138689 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7538 = (7769:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7538
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7539) ≤ val WuPaper.ClassicalFourthData.Bq 7539
    have hp : val WuPaper.ClassicalFourthData.Bq 7539 = (272717225328161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7539 = 272717225328161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7539 = (15539:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7539
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7540) ≤ val WuPaper.ClassicalFourthData.Bq 7540
    have hp : val WuPaper.ClassicalFourthData.Bq 7540 = (272721981971943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7540 = 272721981971943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7540 = (777:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7540
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7541) ≤ val WuPaper.ClassicalFourthData.Bq 7541
    have hp : val WuPaper.ClassicalFourthData.Bq 7541 = (272726736070861:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7541 = 272726736070861 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7541 = (15541:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7541
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7542) ≤ val WuPaper.ClassicalFourthData.Bq 7542
    have hp : val WuPaper.ClassicalFourthData.Bq 7542 = (272731487625743:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7542 = 272731487625743 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7542 = (7771:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7542
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7543) ≤ val WuPaper.ClassicalFourthData.Bq 7543
    have hp : val WuPaper.ClassicalFourthData.Bq 7543 = (272736236637412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7543 = 272736236637412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7543 = (15543:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7543
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7544) ≤ val WuPaper.ClassicalFourthData.Bq 7544
    have hp : val WuPaper.ClassicalFourthData.Bq 7544 = (272740983106696:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7544 = 272740983106696 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7544 = (1943:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7544
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7545) ≤ val WuPaper.ClassicalFourthData.Bq 7545
    have hp : val WuPaper.ClassicalFourthData.Bq 7545 = (272745727034420:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7545 = 272745727034420 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7545 = (3109:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7545
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7546) ≤ val WuPaper.ClassicalFourthData.Bq 7546
    have hp : val WuPaper.ClassicalFourthData.Bq 7546 = (272750468421407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7546 = 272750468421407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7546 = (7773:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7546
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7547) ≤ val WuPaper.ClassicalFourthData.Bq 7547
    have hp : val WuPaper.ClassicalFourthData.Bq 7547 = (272755207268483:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7547 = 272755207268483 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7547 = (15547:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7547
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7548) ≤ val WuPaper.ClassicalFourthData.Bq 7548
    have hp : val WuPaper.ClassicalFourthData.Bq 7548 = (272759943576473:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7548 = 272759943576473 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7548 = (3887:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7548
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7549) ≤ val WuPaper.ClassicalFourthData.Bq 7549
    have hp : val WuPaper.ClassicalFourthData.Bq 7549 = (272764677346199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7549 = 272764677346199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7549 = (15549:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7549
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7550) ≤ val WuPaper.ClassicalFourthData.Bq 7550
    have hp : val WuPaper.ClassicalFourthData.Bq 7550 = (272769408578487:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7550 = 272769408578487 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7550 = (311:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7550
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7551) ≤ val WuPaper.ClassicalFourthData.Bq 7551
    have hp : val WuPaper.ClassicalFourthData.Bq 7551 = (272774137274159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7551 = 272774137274159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7551 = (15551:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7551
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_471
