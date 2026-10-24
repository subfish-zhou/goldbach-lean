import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints511
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_511 (j : Fin 16) (hj : 16*511+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*511+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*511+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8176) ≤ val WuPaper.ClassicalFourthData.Bq 8176
    have hp : val WuPaper.ClassicalFourthData.Bq 8176 = (275265192879109:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8176 = 275265192879109 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8176 = (1011:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8176
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8177) ≤ val WuPaper.ClassicalFourthData.Bq 8177
    have hp : val WuPaper.ClassicalFourthData.Bq 8177 = (275268483750674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8177 = 275268483750674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8177 = (16177:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8177
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8178) ≤ val WuPaper.ClassicalFourthData.Bq 8178
    have hp : val WuPaper.ClassicalFourthData.Bq 8178 = (275271772547950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8178 = 275271772547950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8178 = (8089:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8178
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8179) ≤ val WuPaper.ClassicalFourthData.Bq 8179
    have hp : val WuPaper.ClassicalFourthData.Bq 8179 = (275275059271594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8179 = 275275059271594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8179 = (16179:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8179
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8180) ≤ val WuPaper.ClassicalFourthData.Bq 8180
    have hp : val WuPaper.ClassicalFourthData.Bq 8180 = (275278343922266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8180 = 275278343922266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8180 = (809:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8180
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8181) ≤ val WuPaper.ClassicalFourthData.Bq 8181
    have hp : val WuPaper.ClassicalFourthData.Bq 8181 = (275281626500623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8181 = 275281626500623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8181 = (16181:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8181
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8182) ≤ val WuPaper.ClassicalFourthData.Bq 8182
    have hp : val WuPaper.ClassicalFourthData.Bq 8182 = (275284907007323:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8182 = 275284907007323 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8182 = (8091:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8182
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8183) ≤ val WuPaper.ClassicalFourthData.Bq 8183
    have hp : val WuPaper.ClassicalFourthData.Bq 8183 = (275288185443023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8183 = 275288185443023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8183 = (16183:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8183
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8184) ≤ val WuPaper.ClassicalFourthData.Bq 8184
    have hp : val WuPaper.ClassicalFourthData.Bq 8184 = (275291461808380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8184 = 275291461808380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8184 = (2023:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8184
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8185) ≤ val WuPaper.ClassicalFourthData.Bq 8185
    have hp : val WuPaper.ClassicalFourthData.Bq 8185 = (275294736104053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8185 = 275294736104053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8185 = (3237:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8185
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8186) ≤ val WuPaper.ClassicalFourthData.Bq 8186
    have hp : val WuPaper.ClassicalFourthData.Bq 8186 = (275298008330697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8186 = 275298008330697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8186 = (8093:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8186
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8187) ≤ val WuPaper.ClassicalFourthData.Bq 8187
    have hp : val WuPaper.ClassicalFourthData.Bq 8187 = (275301278488969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8187 = 275301278488969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8187 = (16187:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8187
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8188) ≤ val WuPaper.ClassicalFourthData.Bq 8188
    have hp : val WuPaper.ClassicalFourthData.Bq 8188 = (275304546579525:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8188 = 275304546579525 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8188 = (4047:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8188
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8189) ≤ val WuPaper.ClassicalFourthData.Bq 8189
    have hp : val WuPaper.ClassicalFourthData.Bq 8189 = (275307812603023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8189 = 275307812603023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8189 = (16189:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8189
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8190) ≤ val WuPaper.ClassicalFourthData.Bq 8190
    have hp : val WuPaper.ClassicalFourthData.Bq 8190 = (275311076560117:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8190 = 275311076560117 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8190 = (1619:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8190
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8191) ≤ val WuPaper.ClassicalFourthData.Bq 8191
    have hp : val WuPaper.ClassicalFourthData.Bq 8191 = (275314338451463:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8191 = 275314338451463 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8191 = (16191:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_511
