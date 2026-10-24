import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints559
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_559 (j : Fin 16) (hj : 16*559+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*559+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*559+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8944) ≤ val WuPaper.ClassicalFourthData.Bq 8944
    have hp : val WuPaper.ClassicalFourthData.Bq 8944 = (277228045139842:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8944 = 277228045139842 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8944 = (1059:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8944
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8945) ≤ val WuPaper.ClassicalFourthData.Bq 8945
    have hp : val WuPaper.ClassicalFourthData.Bq 8945 = (277229920826147:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8945 = 277229920826147 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8945 = (3389:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8945
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8946) ≤ val WuPaper.ClassicalFourthData.Bq 8946
    have hp : val WuPaper.ClassicalFourthData.Bq 8946 = (277231794882476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8946 = 277231794882476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8946 = (8473:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8946
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8947) ≤ val WuPaper.ClassicalFourthData.Bq 8947
    have hp : val WuPaper.ClassicalFourthData.Bq 8947 = (277233667309336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8947 = 277233667309336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8947 = (16947:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8947
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8948) ≤ val WuPaper.ClassicalFourthData.Bq 8948
    have hp : val WuPaper.ClassicalFourthData.Bq 8948 = (277235538107233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8948 = 277235538107233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8948 = (4237:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8948
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8949) ≤ val WuPaper.ClassicalFourthData.Bq 8949
    have hp : val WuPaper.ClassicalFourthData.Bq 8949 = (277237407276673:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8949 = 277237407276673 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8949 = (16949:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8949
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8950) ≤ val WuPaper.ClassicalFourthData.Bq 8950
    have hp : val WuPaper.ClassicalFourthData.Bq 8950 = (277239274818161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8950 = 277239274818161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8950 = (339:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8950
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8951) ≤ val WuPaper.ClassicalFourthData.Bq 8951
    have hp : val WuPaper.ClassicalFourthData.Bq 8951 = (277241140732202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8951 = 277241140732202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8951 = (16951:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8951
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8952) ≤ val WuPaper.ClassicalFourthData.Bq 8952
    have hp : val WuPaper.ClassicalFourthData.Bq 8952 = (277243005019302:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8952 = 277243005019302 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8952 = (2119:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8952
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8953) ≤ val WuPaper.ClassicalFourthData.Bq 8953
    have hp : val WuPaper.ClassicalFourthData.Bq 8953 = (277244867679966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8953 = 277244867679966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8953 = (16953:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8953
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8954) ≤ val WuPaper.ClassicalFourthData.Bq 8954
    have hp : val WuPaper.ClassicalFourthData.Bq 8954 = (277246728714699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8954 = 277246728714699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8954 = (8477:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8954
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8955) ≤ val WuPaper.ClassicalFourthData.Bq 8955
    have hp : val WuPaper.ClassicalFourthData.Bq 8955 = (277248588124006:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8955 = 277248588124006 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8955 = (3391:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8955
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8956) ≤ val WuPaper.ClassicalFourthData.Bq 8956
    have hp : val WuPaper.ClassicalFourthData.Bq 8956 = (277250445908391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8956 = 277250445908391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8956 = (4239:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8956
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8957) ≤ val WuPaper.ClassicalFourthData.Bq 8957
    have hp : val WuPaper.ClassicalFourthData.Bq 8957 = (277252302068359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8957 = 277252302068359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8957 = (16957:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8957
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8958) ≤ val WuPaper.ClassicalFourthData.Bq 8958
    have hp : val WuPaper.ClassicalFourthData.Bq 8958 = (277254156604414:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8958 = 277254156604414 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8958 = (8479:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8958
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8959) ≤ val WuPaper.ClassicalFourthData.Bq 8959
    have hp : val WuPaper.ClassicalFourthData.Bq 8959 = (277256009517060:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8959 = 277256009517060 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8959 = (16959:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8959
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_559
