import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints184
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_184 (j : Fin 16) (hj : 16*184+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*184+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*184+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2944) ≤ val WuPaper.ClassicalFourthData.Bq 2944
    have hp : val WuPaper.ClassicalFourthData.Bq 2944 = (201602198917456:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2944 = 201602198917456 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2944 = (342:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2944
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2945) ≤ val WuPaper.ClassicalFourthData.Bq 2945
    have hp : val WuPaper.ClassicalFourthData.Bq 2945 = (201636405696270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2945 = 201636405696270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2945 = (2189:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2945
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2946) ≤ val WuPaper.ClassicalFourthData.Bq 2946
    have hp : val WuPaper.ClassicalFourthData.Bq 2946 = (201670598648636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2946 = 201670598648636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2946 = (5473:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2946
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2947) ≤ val WuPaper.ClassicalFourthData.Bq 2947
    have hp : val WuPaper.ClassicalFourthData.Bq 2947 = (201704777780526:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2947 = 201704777780526 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2947 = (10947:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2947
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2948) ≤ val WuPaper.ClassicalFourthData.Bq 2948
    have hp : val WuPaper.ClassicalFourthData.Bq 2948 = (201738943097906:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2948 = 201738943097906 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2948 = (2737:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2948
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2949) ≤ val WuPaper.ClassicalFourthData.Bq 2949
    have hp : val WuPaper.ClassicalFourthData.Bq 2949 = (201773094606741:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2949 = 201773094606741 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2949 = (10949:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2949
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2950) ≤ val WuPaper.ClassicalFourthData.Bq 2950
    have hp : val WuPaper.ClassicalFourthData.Bq 2950 = (201807232312991:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2950 = 201807232312991 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2950 = (219:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2950
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2951) ≤ val WuPaper.ClassicalFourthData.Bq 2951
    have hp : val WuPaper.ClassicalFourthData.Bq 2951 = (201841356222613:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2951 = 201841356222613 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2951 = (10951:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2951
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2952) ≤ val WuPaper.ClassicalFourthData.Bq 2952
    have hp : val WuPaper.ClassicalFourthData.Bq 2952 = (201875466341564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2952 = 201875466341564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2952 = (1369:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2952
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2953) ≤ val WuPaper.ClassicalFourthData.Bq 2953
    have hp : val WuPaper.ClassicalFourthData.Bq 2953 = (201909562675793:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2953 = 201909562675793 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2953 = (10953:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2953
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2954) ≤ val WuPaper.ClassicalFourthData.Bq 2954
    have hp : val WuPaper.ClassicalFourthData.Bq 2954 = (201943645231251:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2954 = 201943645231251 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2954 = (5477:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2954
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2955) ≤ val WuPaper.ClassicalFourthData.Bq 2955
    have hp : val WuPaper.ClassicalFourthData.Bq 2955 = (201977714013881:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2955 = 201977714013881 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2955 = (2191:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2955
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2956) ≤ val WuPaper.ClassicalFourthData.Bq 2956
    have hp : val WuPaper.ClassicalFourthData.Bq 2956 = (202011769029627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2956 = 202011769029627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2956 = (2739:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2956
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2957) ≤ val WuPaper.ClassicalFourthData.Bq 2957
    have hp : val WuPaper.ClassicalFourthData.Bq 2957 = (202045810284426:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2957 = 202045810284426 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2957 = (10957:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2957
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2958) ≤ val WuPaper.ClassicalFourthData.Bq 2958
    have hp : val WuPaper.ClassicalFourthData.Bq 2958 = (202079837784216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2958 = 202079837784216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2958 = (5479:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2958
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2959) ≤ val WuPaper.ClassicalFourthData.Bq 2959
    have hp : val WuPaper.ClassicalFourthData.Bq 2959 = (202113851534930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2959 = 202113851534930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2959 = (10959:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2959
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_184
