import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints433
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_433 (j : Fin 16) (hj : 16*433+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*433+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*433+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6928) ≤ val WuPaper.ClassicalFourthData.Bq 6928
    have hp : val WuPaper.ClassicalFourthData.Bq 6928 = (269301699278875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6928 = 269301699278875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6928 = (933:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6928
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6929) ≤ val WuPaper.ClassicalFourthData.Bq 6929
    have hp : val WuPaper.ClassicalFourthData.Bq 6929 = (269308177526924:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6929 = 269308177526924 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6929 = (14929:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6929
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6930) ≤ val WuPaper.ClassicalFourthData.Bq 6930
    have hp : val WuPaper.ClassicalFourthData.Bq 6930 = (269314652664106:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6930 = 269314652664106 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6930 = (1493:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6930
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6931) ≤ val WuPaper.ClassicalFourthData.Bq 6931
    have hp : val WuPaper.ClassicalFourthData.Bq 6931 = (269321124691454:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6931 = 269321124691454 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6931 = (14931:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6931
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6932) ≤ val WuPaper.ClassicalFourthData.Bq 6932
    have hp : val WuPaper.ClassicalFourthData.Bq 6932 = (269327593610005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6932 = 269327593610005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6932 = (3733:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6932
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6933) ≤ val WuPaper.ClassicalFourthData.Bq 6933
    have hp : val WuPaper.ClassicalFourthData.Bq 6933 = (269334059420793:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6933 = 269334059420793 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6933 = (14933:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6933
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6934) ≤ val WuPaper.ClassicalFourthData.Bq 6934
    have hp : val WuPaper.ClassicalFourthData.Bq 6934 = (269340522124852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6934 = 269340522124852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6934 = (7467:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6934
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6935) ≤ val WuPaper.ClassicalFourthData.Bq 6935
    have hp : val WuPaper.ClassicalFourthData.Bq 6935 = (269346981723217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6935 = 269346981723217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6935 = (2987:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6935
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6936) ≤ val WuPaper.ClassicalFourthData.Bq 6936
    have hp : val WuPaper.ClassicalFourthData.Bq 6936 = (269353438216920:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6936 = 269353438216920 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6936 = (1867:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6936
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6937) ≤ val WuPaper.ClassicalFourthData.Bq 6937
    have hp : val WuPaper.ClassicalFourthData.Bq 6937 = (269359891606995:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6937 = 269359891606995 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6937 = (14937:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6937
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6938) ≤ val WuPaper.ClassicalFourthData.Bq 6938
    have hp : val WuPaper.ClassicalFourthData.Bq 6938 = (269366341894474:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6938 = 269366341894474 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6938 = (7469:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6938
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6939) ≤ val WuPaper.ClassicalFourthData.Bq 6939
    have hp : val WuPaper.ClassicalFourthData.Bq 6939 = (269372789080390:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6939 = 269372789080390 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6939 = (14939:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6939
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6940) ≤ val WuPaper.ClassicalFourthData.Bq 6940
    have hp : val WuPaper.ClassicalFourthData.Bq 6940 = (269379233165774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6940 = 269379233165774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6940 = (747:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6940
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6941) ≤ val WuPaper.ClassicalFourthData.Bq 6941
    have hp : val WuPaper.ClassicalFourthData.Bq 6941 = (269385674151659:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6941 = 269385674151659 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6941 = (14941:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6941
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6942) ≤ val WuPaper.ClassicalFourthData.Bq 6942
    have hp : val WuPaper.ClassicalFourthData.Bq 6942 = (269392112039076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6942 = 269392112039076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6942 = (7471:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6942
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6943) ≤ val WuPaper.ClassicalFourthData.Bq 6943
    have hp : val WuPaper.ClassicalFourthData.Bq 6943 = (269398546829054:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6943 = 269398546829054 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6943 = (14943:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6943
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_433
