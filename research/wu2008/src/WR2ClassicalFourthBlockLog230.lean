import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints230
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_230 (j : Fin 16) (hj : 16*230+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*230+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*230+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3680) ≤ val WuPaper.ClassicalFourthData.Bq 3680
    have hp : val WuPaper.ClassicalFourthData.Bq 3680 = (223399036314963:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3680 = 223399036314963 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3680 = (73:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3680
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3681) ≤ val WuPaper.ClassicalFourthData.Bq 3681
    have hp : val WuPaper.ClassicalFourthData.Bq 3681 = (223424496497442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3681 = 223424496497442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3681 = (11681:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3681
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3682) ≤ val WuPaper.ClassicalFourthData.Bq 3682
    have hp : val WuPaper.ClassicalFourthData.Bq 3682 = (223449946517317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3682 = 223449946517317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3682 = (5841:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3682
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3683) ≤ val WuPaper.ClassicalFourthData.Bq 3683
    have hp : val WuPaper.ClassicalFourthData.Bq 3683 = (223475386378707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3683 = 223475386378707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3683 = (11683:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3683
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3684) ≤ val WuPaper.ClassicalFourthData.Bq 3684
    have hp : val WuPaper.ClassicalFourthData.Bq 3684 = (223500816085731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3684 = 223500816085731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3684 = (2921:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3684
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3685) ≤ val WuPaper.ClassicalFourthData.Bq 3685
    have hp : val WuPaper.ClassicalFourthData.Bq 3685 = (223526235642506:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3685 = 223526235642506 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3685 = (2337:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3685
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3686) ≤ val WuPaper.ClassicalFourthData.Bq 3686
    have hp : val WuPaper.ClassicalFourthData.Bq 3686 = (223551645053145:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3686 = 223551645053145 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3686 = (5843:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3686
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3687) ≤ val WuPaper.ClassicalFourthData.Bq 3687
    have hp : val WuPaper.ClassicalFourthData.Bq 3687 = (223577044321761:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3687 = 223577044321761 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3687 = (11687:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3687
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3688) ≤ val WuPaper.ClassicalFourthData.Bq 3688
    have hp : val WuPaper.ClassicalFourthData.Bq 3688 = (223602433452465:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3688 = 223602433452465 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3688 = (1461:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3688
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3689) ≤ val WuPaper.ClassicalFourthData.Bq 3689
    have hp : val WuPaper.ClassicalFourthData.Bq 3689 = (223627812449364:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3689 = 223627812449364 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3689 = (11689:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3689
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3690) ≤ val WuPaper.ClassicalFourthData.Bq 3690
    have hp : val WuPaper.ClassicalFourthData.Bq 3690 = (223653181316566:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3690 = 223653181316566 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3690 = (1169:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3690
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3691) ≤ val WuPaper.ClassicalFourthData.Bq 3691
    have hp : val WuPaper.ClassicalFourthData.Bq 3691 = (223678540058174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3691 = 223678540058174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3691 = (11691:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3691
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3692) ≤ val WuPaper.ClassicalFourthData.Bq 3692
    have hp : val WuPaper.ClassicalFourthData.Bq 3692 = (223703888678291:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3692 = 223703888678291 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3692 = (2923:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3692
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3693) ≤ val WuPaper.ClassicalFourthData.Bq 3693
    have hp : val WuPaper.ClassicalFourthData.Bq 3693 = (223729227181017:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3693 = 223729227181017 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3693 = (11693:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3693
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3694) ≤ val WuPaper.ClassicalFourthData.Bq 3694
    have hp : val WuPaper.ClassicalFourthData.Bq 3694 = (223754555570451:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3694 = 223754555570451 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3694 = (5847:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3694
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3695) ≤ val WuPaper.ClassicalFourthData.Bq 3695
    have hp : val WuPaper.ClassicalFourthData.Bq 3695 = (223779873850689:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3695 = 223779873850689 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3695 = (2339:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3695
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_230
