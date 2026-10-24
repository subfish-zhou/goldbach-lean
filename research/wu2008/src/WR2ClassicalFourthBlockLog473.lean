import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints473
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_473 (j : Fin 16) (hj : 16*473+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*473+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*473+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7568) ≤ val WuPaper.ClassicalFourthData.Bq 7568
    have hp : val WuPaper.ClassicalFourthData.Bq 7568 = (272854137794839:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7568 = 272854137794839 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7568 = (973:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7568
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7569) ≤ val WuPaper.ClassicalFourthData.Bq 7569
    have hp : val WuPaper.ClassicalFourthData.Bq 7569 = (272858820971895:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7569 = 272858820971895 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7569 = (15569:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7569
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7570) ≤ val WuPaper.ClassicalFourthData.Bq 7570
    have hp : val WuPaper.ClassicalFourthData.Bq 7570 = (272863501627924:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7570 = 272863501627924 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7570 = (1557:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7570
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7571) ≤ val WuPaper.ClassicalFourthData.Bq 7571
    have hp : val WuPaper.ClassicalFourthData.Bq 7571 = (272868179763743:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7571 = 272868179763743 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7571 = (15571:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7571
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7572) ≤ val WuPaper.ClassicalFourthData.Bq 7572
    have hp : val WuPaper.ClassicalFourthData.Bq 7572 = (272872855380170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7572 = 272872855380170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7572 = (3893:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7572
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7573) ≤ val WuPaper.ClassicalFourthData.Bq 7573
    have hp : val WuPaper.ClassicalFourthData.Bq 7573 = (272877528478021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7573 = 272877528478021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7573 = (15573:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7573
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7574) ≤ val WuPaper.ClassicalFourthData.Bq 7574
    have hp : val WuPaper.ClassicalFourthData.Bq 7574 = (272882199058114:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7574 = 272882199058114 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7574 = (7787:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7574
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7575) ≤ val WuPaper.ClassicalFourthData.Bq 7575
    have hp : val WuPaper.ClassicalFourthData.Bq 7575 = (272886867121263:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7575 = 272886867121263 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7575 = (623:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7575
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7576) ≤ val WuPaper.ClassicalFourthData.Bq 7576
    have hp : val WuPaper.ClassicalFourthData.Bq 7576 = (272891532668286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7576 = 272891532668286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7576 = (1947:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7576
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7577) ≤ val WuPaper.ClassicalFourthData.Bq 7577
    have hp : val WuPaper.ClassicalFourthData.Bq 7577 = (272896195699998:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7577 = 272896195699998 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7577 = (15577:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7577
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7578) ≤ val WuPaper.ClassicalFourthData.Bq 7578
    have hp : val WuPaper.ClassicalFourthData.Bq 7578 = (272900856217214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7578 = 272900856217214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7578 = (7789:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7578
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7579) ≤ val WuPaper.ClassicalFourthData.Bq 7579
    have hp : val WuPaper.ClassicalFourthData.Bq 7579 = (272905514220750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7579 = 272905514220750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7579 = (15579:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7579
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7580) ≤ val WuPaper.ClassicalFourthData.Bq 7580
    have hp : val WuPaper.ClassicalFourthData.Bq 7580 = (272910169711420:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7580 = 272910169711420 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7580 = (779:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7580
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7581) ≤ val WuPaper.ClassicalFourthData.Bq 7581
    have hp : val WuPaper.ClassicalFourthData.Bq 7581 = (272914822690039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7581 = 272914822690039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7581 = (15581:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7581
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7582) ≤ val WuPaper.ClassicalFourthData.Bq 7582
    have hp : val WuPaper.ClassicalFourthData.Bq 7582 = (272919473157421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7582 = 272919473157421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7582 = (7791:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7582
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7583) ≤ val WuPaper.ClassicalFourthData.Bq 7583
    have hp : val WuPaper.ClassicalFourthData.Bq 7583 = (272924121114381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7583 = 272924121114381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7583 = (15583:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7583
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_473
