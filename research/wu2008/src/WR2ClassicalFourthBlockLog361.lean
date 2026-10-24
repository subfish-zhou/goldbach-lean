import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints361
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_361 (j : Fin 16) (hj : 16*361+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*361+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*361+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5776) ≤ val WuPaper.ClassicalFourthData.Bq 5776
    have hp : val WuPaper.ClassicalFourthData.Bq 5776 = (259476202470778:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5776 = 259476202470778 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5776 = (861:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5776
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5777) ≤ val WuPaper.ClassicalFourthData.Bq 5777
    have hp : val WuPaper.ClassicalFourthData.Bq 5777 = (259487066096727:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5777 = 259487066096727 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5777 = (13777:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5777
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5778) ≤ val WuPaper.ClassicalFourthData.Bq 5778
    have hp : val WuPaper.ClassicalFourthData.Bq 5778 = (259497925108600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5778 = 259497925108600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5778 = (6889:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5778
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5779) ≤ val WuPaper.ClassicalFourthData.Bq 5779
    have hp : val WuPaper.ClassicalFourthData.Bq 5779 = (259508779508022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5779 = 259508779508022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5779 = (13779:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5779
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5780) ≤ val WuPaper.ClassicalFourthData.Bq 5780
    have hp : val WuPaper.ClassicalFourthData.Bq 5780 = (259519629296617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5780 = 259519629296617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5780 = (689:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5780
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5781) ≤ val WuPaper.ClassicalFourthData.Bq 5781
    have hp : val WuPaper.ClassicalFourthData.Bq 5781 = (259530474476010:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5781 = 259530474476010 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5781 = (13781:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5781
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5782) ≤ val WuPaper.ClassicalFourthData.Bq 5782
    have hp : val WuPaper.ClassicalFourthData.Bq 5782 = (259541315047826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5782 = 259541315047826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5782 = (6891:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5782
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5783) ≤ val WuPaper.ClassicalFourthData.Bq 5783
    have hp : val WuPaper.ClassicalFourthData.Bq 5783 = (259552151013687:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5783 = 259552151013687 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5783 = (13783:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5783
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5784) ≤ val WuPaper.ClassicalFourthData.Bq 5784
    have hp : val WuPaper.ClassicalFourthData.Bq 5784 = (259562982375215:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5784 = 259562982375215 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5784 = (1723:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5784
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5785) ≤ val WuPaper.ClassicalFourthData.Bq 5785
    have hp : val WuPaper.ClassicalFourthData.Bq 5785 = (259573809134032:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5785 = 259573809134032 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5785 = (2757:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5785
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5786) ≤ val WuPaper.ClassicalFourthData.Bq 5786
    have hp : val WuPaper.ClassicalFourthData.Bq 5786 = (259584631291760:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5786 = 259584631291760 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5786 = (6893:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5786
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5787) ≤ val WuPaper.ClassicalFourthData.Bq 5787
    have hp : val WuPaper.ClassicalFourthData.Bq 5787 = (259595448850019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5787 = 259595448850019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5787 = (13787:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5787
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5788) ≤ val WuPaper.ClassicalFourthData.Bq 5788
    have hp : val WuPaper.ClassicalFourthData.Bq 5788 = (259606261810428:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5788 = 259606261810428 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5788 = (3447:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5788
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5789) ≤ val WuPaper.ClassicalFourthData.Bq 5789
    have hp : val WuPaper.ClassicalFourthData.Bq 5789 = (259617070174607:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5789 = 259617070174607 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5789 = (13789:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5789
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5790) ≤ val WuPaper.ClassicalFourthData.Bq 5790
    have hp : val WuPaper.ClassicalFourthData.Bq 5790 = (259627873944174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5790 = 259627873944174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5790 = (1379:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5790
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5791) ≤ val WuPaper.ClassicalFourthData.Bq 5791
    have hp : val WuPaper.ClassicalFourthData.Bq 5791 = (259638673120747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5791 = 259638673120747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5791 = (13791:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5791
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_361
