import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints236
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_236 (j : Fin 16) (hj : 16*236+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*236+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*236+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3776) ≤ val WuPaper.ClassicalFourthData.Bq 3776
    have hp : val WuPaper.ClassicalFourthData.Bq 3776 = (225797454496688:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3776 = 225797454496688 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3776 = (368:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3776
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3777) ≤ val WuPaper.ClassicalFourthData.Bq 3777
    have hp : val WuPaper.ClassicalFourthData.Bq 3777 = (225821957575925:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3777 = 225821957575925 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3777 = (11777:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3777
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3778) ≤ val WuPaper.ClassicalFourthData.Bq 3778
    have hp : val WuPaper.ClassicalFourthData.Bq 3778 = (225846450879153:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3778 = 225846450879153 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3778 = (5889:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3778
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3779) ≤ val WuPaper.ClassicalFourthData.Bq 3779
    have hp : val WuPaper.ClassicalFourthData.Bq 3779 = (225870934410306:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3779 = 225870934410306 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3779 = (11779:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3779
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3780) ≤ val WuPaper.ClassicalFourthData.Bq 3780
    have hp : val WuPaper.ClassicalFourthData.Bq 3780 = (225895408173314:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3780 = 225895408173314 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3780 = (589:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3780
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3781) ≤ val WuPaper.ClassicalFourthData.Bq 3781
    have hp : val WuPaper.ClassicalFourthData.Bq 3781 = (225919872172109:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3781 = 225919872172109 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3781 = (11781:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3781
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3782) ≤ val WuPaper.ClassicalFourthData.Bq 3782
    have hp : val WuPaper.ClassicalFourthData.Bq 3782 = (225944326410617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3782 = 225944326410617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3782 = (5891:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3782
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3783) ≤ val WuPaper.ClassicalFourthData.Bq 3783
    have hp : val WuPaper.ClassicalFourthData.Bq 3783 = (225968770892765:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3783 = 225968770892765 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3783 = (11783:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3783
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3784) ≤ val WuPaper.ClassicalFourthData.Bq 3784
    have hp : val WuPaper.ClassicalFourthData.Bq 3784 = (225993205622476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3784 = 225993205622476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3784 = (1473:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3784
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3785) ≤ val WuPaper.ClassicalFourthData.Bq 3785
    have hp : val WuPaper.ClassicalFourthData.Bq 3785 = (226017630603673:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3785 = 226017630603673 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3785 = (2357:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3785
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3786) ≤ val WuPaper.ClassicalFourthData.Bq 3786
    have hp : val WuPaper.ClassicalFourthData.Bq 3786 = (226042045840277:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3786 = 226042045840277 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3786 = (5893:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3786
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3787) ≤ val WuPaper.ClassicalFourthData.Bq 3787
    have hp : val WuPaper.ClassicalFourthData.Bq 3787 = (226066451336204:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3787 = 226066451336204 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3787 = (11787:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3787
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3788) ≤ val WuPaper.ClassicalFourthData.Bq 3788
    have hp : val WuPaper.ClassicalFourthData.Bq 3788 = (226090847095373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3788 = 226090847095373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3788 = (2947:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3788
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3789) ≤ val WuPaper.ClassicalFourthData.Bq 3789
    have hp : val WuPaper.ClassicalFourthData.Bq 3789 = (226115233121697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3789 = 226115233121697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3789 = (11789:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3789
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3790) ≤ val WuPaper.ClassicalFourthData.Bq 3790
    have hp : val WuPaper.ClassicalFourthData.Bq 3790 = (226139609419090:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3790 = 226139609419090 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3790 = (1179:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3790
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3791) ≤ val WuPaper.ClassicalFourthData.Bq 3791
    have hp : val WuPaper.ClassicalFourthData.Bq 3791 = (226163975991462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3791 = 226163975991462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3791 = (11791:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3791
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_236
