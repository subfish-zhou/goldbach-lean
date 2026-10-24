import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints244
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_244 (j : Fin 16) (hj : 16*244+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*244+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*244+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3904) ≤ val WuPaper.ClassicalFourthData.Bq 3904
    have hp : val WuPaper.ClassicalFourthData.Bq 3904 = (228855712139005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3904 = 228855712139005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3904 = (372:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3904
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3905) ≤ val WuPaper.ClassicalFourthData.Bq 3905
    have hp : val WuPaper.ClassicalFourthData.Bq 3905 = (228878995226055:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3905 = 228878995226055 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3905 = (2381:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3905
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3906) ≤ val WuPaper.ClassicalFourthData.Bq 3906
    have hp : val WuPaper.ClassicalFourthData.Bq 3906 = (228902269025569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3906 = 228902269025569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3906 = (5953:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3906
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3907) ≤ val WuPaper.ClassicalFourthData.Bq 3907
    have hp : val WuPaper.ClassicalFourthData.Bq 3907 = (228925533541245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3907 = 228925533541245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3907 = (11907:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3907
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3908) ≤ val WuPaper.ClassicalFourthData.Bq 3908
    have hp : val WuPaper.ClassicalFourthData.Bq 3908 = (228948788776782:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3908 = 228948788776782 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3908 = (2977:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3908
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3909) ≤ val WuPaper.ClassicalFourthData.Bq 3909
    have hp : val WuPaper.ClassicalFourthData.Bq 3909 = (228972034735877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3909 = 228972034735877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3909 = (11909:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3909
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3910) ≤ val WuPaper.ClassicalFourthData.Bq 3910
    have hp : val WuPaper.ClassicalFourthData.Bq 3910 = (228995271422224:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3910 = 228995271422224 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3910 = (1191:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3910
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3911) ≤ val WuPaper.ClassicalFourthData.Bq 3911
    have hp : val WuPaper.ClassicalFourthData.Bq 3911 = (229018498839516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3911 = 229018498839516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3911 = (11911:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3911
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3912) ≤ val WuPaper.ClassicalFourthData.Bq 3912
    have hp : val WuPaper.ClassicalFourthData.Bq 3912 = (229041716991445:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3912 = 229041716991445 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3912 = (1489:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3912
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3913) ≤ val WuPaper.ClassicalFourthData.Bq 3913
    have hp : val WuPaper.ClassicalFourthData.Bq 3913 = (229064925881698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3913 = 229064925881698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3913 = (11913:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3913
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3914) ≤ val WuPaper.ClassicalFourthData.Bq 3914
    have hp : val WuPaper.ClassicalFourthData.Bq 3914 = (229088125513965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3914 = 229088125513965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3914 = (5957:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3914
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3915) ≤ val WuPaper.ClassicalFourthData.Bq 3915
    have hp : val WuPaper.ClassicalFourthData.Bq 3915 = (229111315891930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3915 = 229111315891930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3915 = (2383:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3915
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3916) ≤ val WuPaper.ClassicalFourthData.Bq 3916
    have hp : val WuPaper.ClassicalFourthData.Bq 3916 = (229134497019278:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3916 = 229134497019278 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3916 = (2979:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3916
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3917) ≤ val WuPaper.ClassicalFourthData.Bq 3917
    have hp : val WuPaper.ClassicalFourthData.Bq 3917 = (229157668899692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3917 = 229157668899692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3917 = (11917:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3917
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3918) ≤ val WuPaper.ClassicalFourthData.Bq 3918
    have hp : val WuPaper.ClassicalFourthData.Bq 3918 = (229180831536852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3918 = 229180831536852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3918 = (5959:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3918
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3919) ≤ val WuPaper.ClassicalFourthData.Bq 3919
    have hp : val WuPaper.ClassicalFourthData.Bq 3919 = (229203984934436:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3919 = 229203984934436 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3919 = (11919:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3919
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_244
