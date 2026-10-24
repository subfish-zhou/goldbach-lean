import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints630
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_630 (j : Fin 16) (hj : 16*630+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*630+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*630+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10080) ≤ val WuPaper.ClassicalFourthData.Bq 10080
    have hp : val WuPaper.ClassicalFourthData.Bq 10080 = (278420572946418:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10080 = 278420572946418 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10080 = (113:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10080
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10081) ≤ val WuPaper.ClassicalFourthData.Bq 10081
    have hp : val WuPaper.ClassicalFourthData.Bq 10081 = (278420885995963:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10081 = 278420885995963 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10081 = (18081:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10081
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10082) ≤ val WuPaper.ClassicalFourthData.Bq 10082
    have hp : val WuPaper.ClassicalFourthData.Bq 10082 = (278421197895186:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10082 = 278421197895186 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10082 = (9041:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10082
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10083) ≤ val WuPaper.ClassicalFourthData.Bq 10083
    have hp : val WuPaper.ClassicalFourthData.Bq 10083 = (278421508644434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10083 = 278421508644434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10083 = (18083:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10083
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10084) ≤ val WuPaper.ClassicalFourthData.Bq 10084
    have hp : val WuPaper.ClassicalFourthData.Bq 10084 = (278421818244058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10084 = 278421818244058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10084 = (4521:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10084
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10085) ≤ val WuPaper.ClassicalFourthData.Bq 10085
    have hp : val WuPaper.ClassicalFourthData.Bq 10085 = (278422126694406:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10085 = 278422126694406 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10085 = (3617:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10085
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10086) ≤ val WuPaper.ClassicalFourthData.Bq 10086
    have hp : val WuPaper.ClassicalFourthData.Bq 10086 = (278422433995827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10086 = 278422433995827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10086 = (9043:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10086
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10087) ≤ val WuPaper.ClassicalFourthData.Bq 10087
    have hp : val WuPaper.ClassicalFourthData.Bq 10087 = (278422740148671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10087 = 278422740148671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10087 = (18087:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10087
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10088) ≤ val WuPaper.ClassicalFourthData.Bq 10088
    have hp : val WuPaper.ClassicalFourthData.Bq 10088 = (278423045153285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10088 = 278423045153285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10088 = (2261:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10088
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10089) ≤ val WuPaper.ClassicalFourthData.Bq 10089
    have hp : val WuPaper.ClassicalFourthData.Bq 10089 = (278423349010019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10089 = 278423349010019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10089 = (18089:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10089
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10090) ≤ val WuPaper.ClassicalFourthData.Bq 10090
    have hp : val WuPaper.ClassicalFourthData.Bq 10090 = (278423651719221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10090 = 278423651719221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10090 = (1809:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10090
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10091) ≤ val WuPaper.ClassicalFourthData.Bq 10091
    have hp : val WuPaper.ClassicalFourthData.Bq 10091 = (278423953281239:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10091 = 278423953281239 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10091 = (18091:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10091
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10092) ≤ val WuPaper.ClassicalFourthData.Bq 10092
    have hp : val WuPaper.ClassicalFourthData.Bq 10092 = (278424253696422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10092 = 278424253696422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10092 = (4523:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10092
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10093) ≤ val WuPaper.ClassicalFourthData.Bq 10093
    have hp : val WuPaper.ClassicalFourthData.Bq 10093 = (278424552965118:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10093 = 278424552965118 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10093 = (18093:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10093
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10094) ≤ val WuPaper.ClassicalFourthData.Bq 10094
    have hp : val WuPaper.ClassicalFourthData.Bq 10094 = (278424851087674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10094 = 278424851087674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10094 = (9047:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10094
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10095) ≤ val WuPaper.ClassicalFourthData.Bq 10095
    have hp : val WuPaper.ClassicalFourthData.Bq 10095 = (278425148064440:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10095 = 278425148064440 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10095 = (3619:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10095
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_630
