import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints423
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_423 (j : Fin 16) (hj : 16*423+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*423+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*423+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6768) ≤ val WuPaper.ClassicalFourthData.Bq 6768
    have hp : val WuPaper.ClassicalFourthData.Bq 6768 = (268224380222813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6768 = 268224380222813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6768 = (923:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6768
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6769) ≤ val WuPaper.ClassicalFourthData.Bq 6769
    have hp : val WuPaper.ClassicalFourthData.Bq 6769 = (268231369822465:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6769 = 268231369822465 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6769 = (14769:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6769
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6770) ≤ val WuPaper.ClassicalFourthData.Bq 6770
    have hp : val WuPaper.ClassicalFourthData.Bq 6770 = (268238356140434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6770 = 268238356140434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6770 = (1477:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6770
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6771) ≤ val WuPaper.ClassicalFourthData.Bq 6771
    have hp : val WuPaper.ClassicalFourthData.Bq 6771 = (268245339177818:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6771 = 268245339177818 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6771 = (14771:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6771
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6772) ≤ val WuPaper.ClassicalFourthData.Bq 6772
    have hp : val WuPaper.ClassicalFourthData.Bq 6772 = (268252318935718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6772 = 268252318935718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6772 = (3693:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6772
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6773) ≤ val WuPaper.ClassicalFourthData.Bq 6773
    have hp : val WuPaper.ClassicalFourthData.Bq 6773 = (268259295415233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6773 = 268259295415233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6773 = (14773:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6773
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6774) ≤ val WuPaper.ClassicalFourthData.Bq 6774
    have hp : val WuPaper.ClassicalFourthData.Bq 6774 = (268266268617462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6774 = 268266268617462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6774 = (7387:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6774
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6775) ≤ val WuPaper.ClassicalFourthData.Bq 6775
    have hp : val WuPaper.ClassicalFourthData.Bq 6775 = (268273238543504:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6775 = 268273238543504 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6775 = (591:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6775
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6776) ≤ val WuPaper.ClassicalFourthData.Bq 6776
    have hp : val WuPaper.ClassicalFourthData.Bq 6776 = (268280205194456:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6776 = 268280205194456 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6776 = (1847:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6776
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6777) ≤ val WuPaper.ClassicalFourthData.Bq 6777
    have hp : val WuPaper.ClassicalFourthData.Bq 6777 = (268287168571415:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6777 = 268287168571415 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6777 = (14777:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6777
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6778) ≤ val WuPaper.ClassicalFourthData.Bq 6778
    have hp : val WuPaper.ClassicalFourthData.Bq 6778 = (268294128675480:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6778 = 268294128675480 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6778 = (7389:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6778
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6779) ≤ val WuPaper.ClassicalFourthData.Bq 6779
    have hp : val WuPaper.ClassicalFourthData.Bq 6779 = (268301085507747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6779 = 268301085507747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6779 = (14779:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6779
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6780) ≤ val WuPaper.ClassicalFourthData.Bq 6780
    have hp : val WuPaper.ClassicalFourthData.Bq 6780 = (268308039069312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6780 = 268308039069312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6780 = (739:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6780
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6781) ≤ val WuPaper.ClassicalFourthData.Bq 6781
    have hp : val WuPaper.ClassicalFourthData.Bq 6781 = (268314989361272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6781 = 268314989361272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6781 = (14781:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6781
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6782) ≤ val WuPaper.ClassicalFourthData.Bq 6782
    have hp : val WuPaper.ClassicalFourthData.Bq 6782 = (268321936384721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6782 = 268321936384721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6782 = (7391:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6782
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6783) ≤ val WuPaper.ClassicalFourthData.Bq 6783
    have hp : val WuPaper.ClassicalFourthData.Bq 6783 = (268328880140755:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6783 = 268328880140755 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6783 = (14783:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6783
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_423
