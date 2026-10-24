import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints263
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_263 (j : Fin 16) (hj : 16*263+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*263+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*263+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4208) ≤ val WuPaper.ClassicalFourthData.Bq 4208
    have hp : val WuPaper.ClassicalFourthData.Bq 4208 = (235522584308167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4208 = 235522584308167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4208 = (763:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4208
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4209) ≤ val WuPaper.ClassicalFourthData.Bq 4209
    have hp : val WuPaper.ClassicalFourthData.Bq 4209 = (235543206567693:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4209 = 235543206567693 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4209 = (12209:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4209
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4210) ≤ val WuPaper.ClassicalFourthData.Bq 4210
    have hp : val WuPaper.ClassicalFourthData.Bq 4210 = (235563820587862:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4210 = 235563820587862 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4210 = (1221:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4210
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4211) ≤ val WuPaper.ClassicalFourthData.Bq 4211
    have hp : val WuPaper.ClassicalFourthData.Bq 4211 = (235584426371882:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4211 = 235584426371882 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4211 = (12211:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4211
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4212) ≤ val WuPaper.ClassicalFourthData.Bq 4212
    have hp : val WuPaper.ClassicalFourthData.Bq 4212 = (235605023922960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4212 = 235605023922960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4212 = (3053:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4212
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4213) ≤ val WuPaper.ClassicalFourthData.Bq 4213
    have hp : val WuPaper.ClassicalFourthData.Bq 4213 = (235625613244302:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4213 = 235625613244302 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4213 = (12213:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4213
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4214) ≤ val WuPaper.ClassicalFourthData.Bq 4214
    have hp : val WuPaper.ClassicalFourthData.Bq 4214 = (235646194339112:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4214 = 235646194339112 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4214 = (6107:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4214
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4215) ≤ val WuPaper.ClassicalFourthData.Bq 4215
    have hp : val WuPaper.ClassicalFourthData.Bq 4215 = (235666767210591:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4215 = 235666767210591 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4215 = (2443:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4215
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4216) ≤ val WuPaper.ClassicalFourthData.Bq 4216
    have hp : val WuPaper.ClassicalFourthData.Bq 4216 = (235687331861941:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4216 = 235687331861941 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4216 = (1527:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4216
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4217) ≤ val WuPaper.ClassicalFourthData.Bq 4217
    have hp : val WuPaper.ClassicalFourthData.Bq 4217 = (235707888296361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4217 = 235707888296361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4217 = (12217:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4217
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4218) ≤ val WuPaper.ClassicalFourthData.Bq 4218
    have hp : val WuPaper.ClassicalFourthData.Bq 4218 = (235728436517050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4218 = 235728436517050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4218 = (6109:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4218
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4219) ≤ val WuPaper.ClassicalFourthData.Bq 4219
    have hp : val WuPaper.ClassicalFourthData.Bq 4219 = (235748976527203:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4219 = 235748976527203 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4219 = (12219:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4219
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4220) ≤ val WuPaper.ClassicalFourthData.Bq 4220
    have hp : val WuPaper.ClassicalFourthData.Bq 4220 = (235769508330016:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4220 = 235769508330016 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4220 = (611:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4220
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4221) ≤ val WuPaper.ClassicalFourthData.Bq 4221
    have hp : val WuPaper.ClassicalFourthData.Bq 4221 = (235790031928683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4221 = 235790031928683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4221 = (12221:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4221
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4222) ≤ val WuPaper.ClassicalFourthData.Bq 4222
    have hp : val WuPaper.ClassicalFourthData.Bq 4222 = (235810547326394:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4222 = 235810547326394 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4222 = (6111:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4222
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4223) ≤ val WuPaper.ClassicalFourthData.Bq 4223
    have hp : val WuPaper.ClassicalFourthData.Bq 4223 = (235831054526342:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4223 = 235831054526342 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4223 = (12223:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4223
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_263
