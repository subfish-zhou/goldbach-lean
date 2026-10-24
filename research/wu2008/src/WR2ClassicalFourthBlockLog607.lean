import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints607
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_607 (j : Fin 16) (hj : 16*607+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*607+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*607+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9712) ≤ val WuPaper.ClassicalFourthData.Bq 9712
    have hp : val WuPaper.ClassicalFourthData.Bq 9712 = (278224254922256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9712 = 278224254922256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9712 = (1107:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9712
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9713) ≤ val WuPaper.ClassicalFourthData.Bq 9713
    have hp : val WuPaper.ClassicalFourthData.Bq 9713 = (278225015967513:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9713 = 278225015967513 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9713 = (17713:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9713
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9714) ≤ val WuPaper.ClassicalFourthData.Bq 9714
    have hp : val WuPaper.ClassicalFourthData.Bq 9714 = (278225775726023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9714 = 278225775726023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9714 = (8857:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9714
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9715) ≤ val WuPaper.ClassicalFourthData.Bq 9715
    have hp : val WuPaper.ClassicalFourthData.Bq 9715 = (278226534198179:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9715 = 278226534198179 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9715 = (3543:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9715
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9716) ≤ val WuPaper.ClassicalFourthData.Bq 9716
    have hp : val WuPaper.ClassicalFourthData.Bq 9716 = (278227291384374:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9716 = 278227291384374 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9716 = (4429:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9716
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9717) ≤ val WuPaper.ClassicalFourthData.Bq 9717
    have hp : val WuPaper.ClassicalFourthData.Bq 9717 = (278228047285000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9717 = 278228047285000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9717 = (17717:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9717
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9718) ≤ val WuPaper.ClassicalFourthData.Bq 9718
    have hp : val WuPaper.ClassicalFourthData.Bq 9718 = (278228801900450:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9718 = 278228801900450 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9718 = (8859:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9718
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9719) ≤ val WuPaper.ClassicalFourthData.Bq 9719
    have hp : val WuPaper.ClassicalFourthData.Bq 9719 = (278229555231117:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9719 = 278229555231117 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9719 = (17719:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9719
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9720) ≤ val WuPaper.ClassicalFourthData.Bq 9720
    have hp : val WuPaper.ClassicalFourthData.Bq 9720 = (278230307277393:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9720 = 278230307277393 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9720 = (443:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9720
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9721) ≤ val WuPaper.ClassicalFourthData.Bq 9721
    have hp : val WuPaper.ClassicalFourthData.Bq 9721 = (278231058039670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9721 = 278231058039670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9721 = (17721:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9721
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9722) ≤ val WuPaper.ClassicalFourthData.Bq 9722
    have hp : val WuPaper.ClassicalFourthData.Bq 9722 = (278231807518341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9722 = 278231807518341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9722 = (8861:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9722
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9723) ≤ val WuPaper.ClassicalFourthData.Bq 9723
    have hp : val WuPaper.ClassicalFourthData.Bq 9723 = (278232555713797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9723 = 278232555713797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9723 = (17723:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9723
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9724) ≤ val WuPaper.ClassicalFourthData.Bq 9724
    have hp : val WuPaper.ClassicalFourthData.Bq 9724 = (278233302626430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9724 = 278233302626430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9724 = (4431:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9724
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9725) ≤ val WuPaper.ClassicalFourthData.Bq 9725
    have hp : val WuPaper.ClassicalFourthData.Bq 9725 = (278234048256632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9725 = 278234048256632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9725 = (709:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9725
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9726) ≤ val WuPaper.ClassicalFourthData.Bq 9726
    have hp : val WuPaper.ClassicalFourthData.Bq 9726 = (278234792604795:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9726 = 278234792604795 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9726 = (8863:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9726
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9727) ≤ val WuPaper.ClassicalFourthData.Bq 9727
    have hp : val WuPaper.ClassicalFourthData.Bq 9727 = (278235535671310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9727 = 278235535671310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9727 = (17727:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9727
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_607
