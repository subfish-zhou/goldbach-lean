import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints233
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_233 (j : Fin 16) (hj : 16*233+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*233+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*233+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3728) ≤ val WuPaper.ClassicalFourthData.Bq 3728
    have hp : val WuPaper.ClassicalFourthData.Bq 3728 = (224609732534218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3728 = 224609732534218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3728 = (733:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3728
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3729) ≤ val WuPaper.ClassicalFourthData.Bq 3729
    have hp : val WuPaper.ClassicalFourthData.Bq 3729 = (224634709525056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3729 = 224634709525056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3729 = (11729:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3729
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3730) ≤ val WuPaper.ClassicalFourthData.Bq 3730
    have hp : val WuPaper.ClassicalFourthData.Bq 3730 = (224659676548829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3730 = 224659676548829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3730 = (1173:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3730
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3731) ≤ val WuPaper.ClassicalFourthData.Bq 3731
    have hp : val WuPaper.ClassicalFourthData.Bq 3731 = (224684633609564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3731 = 224684633609564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3731 = (11731:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3731
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3732) ≤ val WuPaper.ClassicalFourthData.Bq 3732
    have hp : val WuPaper.ClassicalFourthData.Bq 3732 = (224709580711284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3732 = 224709580711284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3732 = (2933:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3732
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3733) ≤ val WuPaper.ClassicalFourthData.Bq 3733
    have hp : val WuPaper.ClassicalFourthData.Bq 3733 = (224734517858010:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3733 = 224734517858010 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3733 = (11733:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3733
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3734) ≤ val WuPaper.ClassicalFourthData.Bq 3734
    have hp : val WuPaper.ClassicalFourthData.Bq 3734 = (224759445053764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3734 = 224759445053764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3734 = (5867:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3734
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3735) ≤ val WuPaper.ClassicalFourthData.Bq 3735
    have hp : val WuPaper.ClassicalFourthData.Bq 3735 = (224784362302562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3735 = 224784362302562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3735 = (2347:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3735
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3736) ≤ val WuPaper.ClassicalFourthData.Bq 3736
    have hp : val WuPaper.ClassicalFourthData.Bq 3736 = (224809269608420:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3736 = 224809269608420 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3736 = (1467:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3736
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3737) ≤ val WuPaper.ClassicalFourthData.Bq 3737
    have hp : val WuPaper.ClassicalFourthData.Bq 3737 = (224834166975353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3737 = 224834166975353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3737 = (11737:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3737
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3738) ≤ val WuPaper.ClassicalFourthData.Bq 3738
    have hp : val WuPaper.ClassicalFourthData.Bq 3738 = (224859054407372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3738 = 224859054407372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3738 = (5869:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3738
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3739) ≤ val WuPaper.ClassicalFourthData.Bq 3739
    have hp : val WuPaper.ClassicalFourthData.Bq 3739 = (224883931908487:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3739 = 224883931908487 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3739 = (11739:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3739
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3740) ≤ val WuPaper.ClassicalFourthData.Bq 3740
    have hp : val WuPaper.ClassicalFourthData.Bq 3740 = (224908799482708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3740 = 224908799482708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3740 = (587:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3740
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3741) ≤ val WuPaper.ClassicalFourthData.Bq 3741
    have hp : val WuPaper.ClassicalFourthData.Bq 3741 = (224933657134039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3741 = 224933657134039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3741 = (11741:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3741
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3742) ≤ val WuPaper.ClassicalFourthData.Bq 3742
    have hp : val WuPaper.ClassicalFourthData.Bq 3742 = (224958504866485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3742 = 224958504866485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3742 = (5871:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3742
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3743) ≤ val WuPaper.ClassicalFourthData.Bq 3743
    have hp : val WuPaper.ClassicalFourthData.Bq 3743 = (224983342684049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3743 = 224983342684049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3743 = (11743:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3743
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_233
