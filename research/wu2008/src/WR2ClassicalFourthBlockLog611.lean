import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints611
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_611 (j : Fin 16) (hj : 16*611+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*611+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*611+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9776) ≤ val WuPaper.ClassicalFourthData.Bq 9776
    have hp : val WuPaper.ClassicalFourthData.Bq 9776 = (278270384030662:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9776 = 278270384030662 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9776 = (1111:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9776
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9777) ≤ val WuPaper.ClassicalFourthData.Bq 9777
    have hp : val WuPaper.ClassicalFourthData.Bq 9777 = (278271063511156:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9777 = 278271063511156 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9777 = (17777:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9777
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9778) ≤ val WuPaper.ClassicalFourthData.Bq 9778
    have hp : val WuPaper.ClassicalFourthData.Bq 9778 = (278271741729802:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9778 = 278271741729802 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9778 = (8889:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9778
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9779) ≤ val WuPaper.ClassicalFourthData.Bq 9779
    have hp : val WuPaper.ClassicalFourthData.Bq 9779 = (278272418686985:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9779 = 278272418686985 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9779 = (17779:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9779
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9780) ≤ val WuPaper.ClassicalFourthData.Bq 9780
    have hp : val WuPaper.ClassicalFourthData.Bq 9780 = (278273094383089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9780 = 278273094383089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9780 = (889:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9780
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9781) ≤ val WuPaper.ClassicalFourthData.Bq 9781
    have hp : val WuPaper.ClassicalFourthData.Bq 9781 = (278273768818499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9781 = 278273768818499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9781 = (17781:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9781
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9782) ≤ val WuPaper.ClassicalFourthData.Bq 9782
    have hp : val WuPaper.ClassicalFourthData.Bq 9782 = (278274441993600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9782 = 278274441993600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9782 = (8891:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9782
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9783) ≤ val WuPaper.ClassicalFourthData.Bq 9783
    have hp : val WuPaper.ClassicalFourthData.Bq 9783 = (278275113908777:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9783 = 278275113908777 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9783 = (17783:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9783
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9784) ≤ val WuPaper.ClassicalFourthData.Bq 9784
    have hp : val WuPaper.ClassicalFourthData.Bq 9784 = (278275784564413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9784 = 278275784564413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9784 = (2223:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9784
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9785) ≤ val WuPaper.ClassicalFourthData.Bq 9785
    have hp : val WuPaper.ClassicalFourthData.Bq 9785 = (278276453960893:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9785 = 278276453960893 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9785 = (3557:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9785
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9786) ≤ val WuPaper.ClassicalFourthData.Bq 9786
    have hp : val WuPaper.ClassicalFourthData.Bq 9786 = (278277122098601:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9786 = 278277122098601 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9786 = (8893:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9786
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9787) ≤ val WuPaper.ClassicalFourthData.Bq 9787
    have hp : val WuPaper.ClassicalFourthData.Bq 9787 = (278277788977921:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9787 = 278277788977921 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9787 = (17787:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9787
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9788) ≤ val WuPaper.ClassicalFourthData.Bq 9788
    have hp : val WuPaper.ClassicalFourthData.Bq 9788 = (278278454599237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9788 = 278278454599237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9788 = (4447:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9788
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9789) ≤ val WuPaper.ClassicalFourthData.Bq 9789
    have hp : val WuPaper.ClassicalFourthData.Bq 9789 = (278279118962932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9789 = 278279118962932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9789 = (17789:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9789
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9790) ≤ val WuPaper.ClassicalFourthData.Bq 9790
    have hp : val WuPaper.ClassicalFourthData.Bq 9790 = (278279782069391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9790 = 278279782069391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9790 = (1779:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9790
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9791) ≤ val WuPaper.ClassicalFourthData.Bq 9791
    have hp : val WuPaper.ClassicalFourthData.Bq 9791 = (278280443918996:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9791 = 278280443918996 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9791 = (17791:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9791
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_611
