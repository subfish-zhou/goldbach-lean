import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints474
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_474 (j : Fin 16) (hj : 16*474+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*474+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*474+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7584) ≤ val WuPaper.ClassicalFourthData.Bq 7584
    have hp : val WuPaper.ClassicalFourthData.Bq 7584 = (272928766561730:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7584 = 272928766561730 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7584 = (487:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7584
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7585) ≤ val WuPaper.ClassicalFourthData.Bq 7585
    have hp : val WuPaper.ClassicalFourthData.Bq 7585 = (272933409500284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7585 = 272933409500284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7585 = (3117:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7585
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7586) ≤ val WuPaper.ClassicalFourthData.Bq 7586
    have hp : val WuPaper.ClassicalFourthData.Bq 7586 = (272938049930856:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7586 = 272938049930856 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7586 = (7793:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7586
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7587) ≤ val WuPaper.ClassicalFourthData.Bq 7587
    have hp : val WuPaper.ClassicalFourthData.Bq 7587 = (272942687854256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7587 = 272942687854256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7587 = (15587:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7587
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7588) ≤ val WuPaper.ClassicalFourthData.Bq 7588
    have hp : val WuPaper.ClassicalFourthData.Bq 7588 = (272947323271300:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7588 = 272947323271300 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7588 = (3897:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7588
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7589) ≤ val WuPaper.ClassicalFourthData.Bq 7589
    have hp : val WuPaper.ClassicalFourthData.Bq 7589 = (272951956182797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7589 = 272951956182797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7589 = (15589:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7589
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7590) ≤ val WuPaper.ClassicalFourthData.Bq 7590
    have hp : val WuPaper.ClassicalFourthData.Bq 7590 = (272956586589561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7590 = 272956586589561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7590 = (1559:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7590
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7591) ≤ val WuPaper.ClassicalFourthData.Bq 7591
    have hp : val WuPaper.ClassicalFourthData.Bq 7591 = (272961214492404:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7591 = 272961214492404 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7591 = (15591:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7591
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7592) ≤ val WuPaper.ClassicalFourthData.Bq 7592
    have hp : val WuPaper.ClassicalFourthData.Bq 7592 = (272965839892135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7592 = 272965839892135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7592 = (1949:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7592
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7593) ≤ val WuPaper.ClassicalFourthData.Bq 7593
    have hp : val WuPaper.ClassicalFourthData.Bq 7593 = (272970462789566:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7593 = 272970462789566 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7593 = (15593:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7593
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7594) ≤ val WuPaper.ClassicalFourthData.Bq 7594
    have hp : val WuPaper.ClassicalFourthData.Bq 7594 = (272975083185509:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7594 = 272975083185509 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7594 = (7797:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7594
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7595) ≤ val WuPaper.ClassicalFourthData.Bq 7595
    have hp : val WuPaper.ClassicalFourthData.Bq 7595 = (272979701080773:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7595 = 272979701080773 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7595 = (3119:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7595
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7596) ≤ val WuPaper.ClassicalFourthData.Bq 7596
    have hp : val WuPaper.ClassicalFourthData.Bq 7596 = (272984316476168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7596 = 272984316476168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7596 = (3899:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7596
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7597) ≤ val WuPaper.ClassicalFourthData.Bq 7597
    have hp : val WuPaper.ClassicalFourthData.Bq 7597 = (272988929372505:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7597 = 272988929372505 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7597 = (15597:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7597
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7598) ≤ val WuPaper.ClassicalFourthData.Bq 7598
    have hp : val WuPaper.ClassicalFourthData.Bq 7598 = (272993539770592:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7598 = 272993539770592 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7598 = (7799:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7598
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7599) ≤ val WuPaper.ClassicalFourthData.Bq 7599
    have hp : val WuPaper.ClassicalFourthData.Bq 7599 = (272998147671239:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7599 = 272998147671239 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7599 = (15599:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7599
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_474
