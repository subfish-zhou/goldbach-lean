import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints484
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_484 (j : Fin 16) (hj : 16*484+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*484+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*484+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7744) ≤ val WuPaper.ClassicalFourthData.Bq 7744
    have hp : val WuPaper.ClassicalFourthData.Bq 7744 = (273640272041093:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7744 = 273640272041093 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7744 = (492:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7744
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7745) ≤ val WuPaper.ClassicalFourthData.Bq 7745
    have hp : val WuPaper.ClassicalFourthData.Bq 7745 = (273644523846926:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7745 = 273644523846926 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7745 = (3149:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7745
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7746) ≤ val WuPaper.ClassicalFourthData.Bq 7746
    have hp : val WuPaper.ClassicalFourthData.Bq 7746 = (273648773271159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7746 = 273648773271159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7746 = (7873:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7746
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7747) ≤ val WuPaper.ClassicalFourthData.Bq 7747
    have hp : val WuPaper.ClassicalFourthData.Bq 7747 = (273653020314559:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7747 = 273653020314559 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7747 = (15747:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7747
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7748) ≤ val WuPaper.ClassicalFourthData.Bq 7748
    have hp : val WuPaper.ClassicalFourthData.Bq 7748 = (273657264977894:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7748 = 273657264977894 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7748 = (3937:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7748
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7749) ≤ val WuPaper.ClassicalFourthData.Bq 7749
    have hp : val WuPaper.ClassicalFourthData.Bq 7749 = (273661507261930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7749 = 273661507261930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7749 = (15749:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7749
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7750) ≤ val WuPaper.ClassicalFourthData.Bq 7750
    have hp : val WuPaper.ClassicalFourthData.Bq 7750 = (273665747167434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7750 = 273665747167434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7750 = (63:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7750
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7751) ≤ val WuPaper.ClassicalFourthData.Bq 7751
    have hp : val WuPaper.ClassicalFourthData.Bq 7751 = (273669984695171:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7751 = 273669984695171 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7751 = (15751:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7751
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7752) ≤ val WuPaper.ClassicalFourthData.Bq 7752
    have hp : val WuPaper.ClassicalFourthData.Bq 7752 = (273674219845908:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7752 = 273674219845908 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7752 = (1969:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7752
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7753) ≤ val WuPaper.ClassicalFourthData.Bq 7753
    have hp : val WuPaper.ClassicalFourthData.Bq 7753 = (273678452620410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7753 = 273678452620410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7753 = (15753:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7753
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7754) ≤ val WuPaper.ClassicalFourthData.Bq 7754
    have hp : val WuPaper.ClassicalFourthData.Bq 7754 = (273682683019442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7754 = 273682683019442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7754 = (7877:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7754
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7755) ≤ val WuPaper.ClassicalFourthData.Bq 7755
    have hp : val WuPaper.ClassicalFourthData.Bq 7755 = (273686911043770:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7755 = 273686911043770 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7755 = (3151:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7755
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7756) ≤ val WuPaper.ClassicalFourthData.Bq 7756
    have hp : val WuPaper.ClassicalFourthData.Bq 7756 = (273691136694159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7756 = 273691136694159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7756 = (3939:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7756
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7757) ≤ val WuPaper.ClassicalFourthData.Bq 7757
    have hp : val WuPaper.ClassicalFourthData.Bq 7757 = (273695359971372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7757 = 273695359971372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7757 = (15757:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7757
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7758) ≤ val WuPaper.ClassicalFourthData.Bq 7758
    have hp : val WuPaper.ClassicalFourthData.Bq 7758 = (273699580876175:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7758 = 273699580876175 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7758 = (7879:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7758
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7759) ≤ val WuPaper.ClassicalFourthData.Bq 7759
    have hp : val WuPaper.ClassicalFourthData.Bq 7759 = (273703799409331:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7759 = 273703799409331 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7759 = (15759:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7759
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_484
