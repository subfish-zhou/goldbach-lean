import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints294
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_294 (j : Fin 16) (hj : 16*294+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*294+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*294+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4704) ≤ val WuPaper.ClassicalFourthData.Bq 4704
    have hp : val WuPaper.ClassicalFourthData.Bq 4704 = (244801111144111:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4704 = 244801111144111 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4704 = (397:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4704
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4705) ≤ val WuPaper.ClassicalFourthData.Bq 4705
    have hp : val WuPaper.ClassicalFourthData.Bq 4705 = (244818012467615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4705 = 244818012467615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4705 = (2541:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4705
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4706) ≤ val WuPaper.ClassicalFourthData.Bq 4706
    have hp : val WuPaper.ClassicalFourthData.Bq 4706 = (244834906976300:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4706 = 244834906976300 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4706 = (6353:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4706
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4707) ≤ val WuPaper.ClassicalFourthData.Bq 4707
    have hp : val WuPaper.ClassicalFourthData.Bq 4707 = (244851794672728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4707 = 244851794672728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4707 = (12707:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4707
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4708) ≤ val WuPaper.ClassicalFourthData.Bq 4708
    have hp : val WuPaper.ClassicalFourthData.Bq 4708 = (244868675559462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4708 = 244868675559462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4708 = (3177:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4708
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4709) ≤ val WuPaper.ClassicalFourthData.Bq 4709
    have hp : val WuPaper.ClassicalFourthData.Bq 4709 = (244885549639063:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4709 = 244885549639063 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4709 = (12709:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4709
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4710) ≤ val WuPaper.ClassicalFourthData.Bq 4710
    have hp : val WuPaper.ClassicalFourthData.Bq 4710 = (244902416914091:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4710 = 244902416914091 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4710 = (1271:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4710
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4711) ≤ val WuPaper.ClassicalFourthData.Bq 4711
    have hp : val WuPaper.ClassicalFourthData.Bq 4711 = (244919277387103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4711 = 244919277387103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4711 = (12711:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4711
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4712) ≤ val WuPaper.ClassicalFourthData.Bq 4712
    have hp : val WuPaper.ClassicalFourthData.Bq 4712 = (244936131060658:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4712 = 244936131060658 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4712 = (1589:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4712
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4713) ≤ val WuPaper.ClassicalFourthData.Bq 4713
    have hp : val WuPaper.ClassicalFourthData.Bq 4713 = (244952977937312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4713 = 244952977937312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4713 = (12713:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4713
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4714) ≤ val WuPaper.ClassicalFourthData.Bq 4714
    have hp : val WuPaper.ClassicalFourthData.Bq 4714 = (244969818019620:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4714 = 244969818019620 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4714 = (6357:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4714
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4715) ≤ val WuPaper.ClassicalFourthData.Bq 4715
    have hp : val WuPaper.ClassicalFourthData.Bq 4715 = (244986651310136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4715 = 244986651310136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4715 = (2543:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4715
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4716) ≤ val WuPaper.ClassicalFourthData.Bq 4716
    have hp : val WuPaper.ClassicalFourthData.Bq 4716 = (245003477811414:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4716 = 245003477811414 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4716 = (3179:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4716
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4717) ≤ val WuPaper.ClassicalFourthData.Bq 4717
    have hp : val WuPaper.ClassicalFourthData.Bq 4717 = (245020297526005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4717 = 245020297526005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4717 = (12717:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4717
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4718) ≤ val WuPaper.ClassicalFourthData.Bq 4718
    have hp : val WuPaper.ClassicalFourthData.Bq 4718 = (245037110456459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4718 = 245037110456459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4718 = (6359:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4718
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4719) ≤ val WuPaper.ClassicalFourthData.Bq 4719
    have hp : val WuPaper.ClassicalFourthData.Bq 4719 = (245053916605327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4719 = 245053916605327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4719 = (12719:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4719
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_294
