import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints238
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_238 (j : Fin 16) (hj : 16*238+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*238+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*238+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3808) ≤ val WuPaper.ClassicalFourthData.Bq 3808
    have hp : val WuPaper.ClassicalFourthData.Bq 3808 = (226576723574154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3808 = 226576723574154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3808 = (369:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3808
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3809) ≤ val WuPaper.ClassicalFourthData.Bq 3809
    have hp : val WuPaper.ClassicalFourthData.Bq 3809 = (226600915762774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3809 = 226600915762774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3809 = (11809:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3809
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3810) ≤ val WuPaper.ClassicalFourthData.Bq 3810
    have hp : val WuPaper.ClassicalFourthData.Bq 3810 = (226625098300324:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3810 = 226625098300324 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3810 = (1181:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3810
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3811) ≤ val WuPaper.ClassicalFourthData.Bq 3811
    have hp : val WuPaper.ClassicalFourthData.Bq 3811 = (226649271190677:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3811 = 226649271190677 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3811 = (11811:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3811
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3812) ≤ val WuPaper.ClassicalFourthData.Bq 3812
    have hp : val WuPaper.ClassicalFourthData.Bq 3812 = (226673434437705:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3812 = 226673434437705 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3812 = (2953:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3812
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3813) ≤ val WuPaper.ClassicalFourthData.Bq 3813
    have hp : val WuPaper.ClassicalFourthData.Bq 3813 = (226697588045278:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3813 = 226697588045278 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3813 = (11813:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3813
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3814) ≤ val WuPaper.ClassicalFourthData.Bq 3814
    have hp : val WuPaper.ClassicalFourthData.Bq 3814 = (226721732017264:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3814 = 226721732017264 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3814 = (5907:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3814
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3815) ≤ val WuPaper.ClassicalFourthData.Bq 3815
    have hp : val WuPaper.ClassicalFourthData.Bq 3815 = (226745866357529:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3815 = 226745866357529 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3815 = (2363:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3815
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3816) ≤ val WuPaper.ClassicalFourthData.Bq 3816
    have hp : val WuPaper.ClassicalFourthData.Bq 3816 = (226769991069937:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3816 = 226769991069937 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3816 = (1477:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3816
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3817) ≤ val WuPaper.ClassicalFourthData.Bq 3817
    have hp : val WuPaper.ClassicalFourthData.Bq 3817 = (226794106158350:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3817 = 226794106158350 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3817 = (11817:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3817
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3818) ≤ val WuPaper.ClassicalFourthData.Bq 3818
    have hp : val WuPaper.ClassicalFourthData.Bq 3818 = (226818211626629:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3818 = 226818211626629 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3818 = (5909:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3818
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3819) ≤ val WuPaper.ClassicalFourthData.Bq 3819
    have hp : val WuPaper.ClassicalFourthData.Bq 3819 = (226842307478632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3819 = 226842307478632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3819 = (11819:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3819
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3820) ≤ val WuPaper.ClassicalFourthData.Bq 3820
    have hp : val WuPaper.ClassicalFourthData.Bq 3820 = (226866393718217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3820 = 226866393718217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3820 = (591:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3820
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3821) ≤ val WuPaper.ClassicalFourthData.Bq 3821
    have hp : val WuPaper.ClassicalFourthData.Bq 3821 = (226890470349238:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3821 = 226890470349238 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3821 = (11821:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3821
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3822) ≤ val WuPaper.ClassicalFourthData.Bq 3822
    have hp : val WuPaper.ClassicalFourthData.Bq 3822 = (226914537375548:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3822 = 226914537375548 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3822 = (5911:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3822
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3823) ≤ val WuPaper.ClassicalFourthData.Bq 3823
    have hp : val WuPaper.ClassicalFourthData.Bq 3823 = (226938594801000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3823 = 226938594801000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3823 = (11823:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3823
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_238
