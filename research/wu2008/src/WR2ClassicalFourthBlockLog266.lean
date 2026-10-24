import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints266
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_266 (j : Fin 16) (hj : 16*266+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*266+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*266+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4256) ≤ val WuPaper.ClassicalFourthData.Bq 4256
    have hp : val WuPaper.ClassicalFourthData.Bq 4256 = (236503213974973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4256 = 236503213974973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4256 = (383:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4256
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4257) ≤ val WuPaper.ClassicalFourthData.Bq 4257
    have hp : val WuPaper.ClassicalFourthData.Bq 4257 = (236523444338877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4257 = 236523444338877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4257 = (12257:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4257
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4258) ≤ val WuPaper.ClassicalFourthData.Bq 4258
    have hp : val WuPaper.ClassicalFourthData.Bq 4258 = (236543666615764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4258 = 236543666615764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4258 = (6129:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4258
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4259) ≤ val WuPaper.ClassicalFourthData.Bq 4259
    have hp : val WuPaper.ClassicalFourthData.Bq 4259 = (236563880808774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4259 = 236563880808774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4259 = (12259:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4259
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4260) ≤ val WuPaper.ClassicalFourthData.Bq 4260
    have hp : val WuPaper.ClassicalFourthData.Bq 4260 = (236584086921043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4260 = 236584086921043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4260 = (613:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4260
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4261) ≤ val WuPaper.ClassicalFourthData.Bq 4261
    have hp : val WuPaper.ClassicalFourthData.Bq 4261 = (236604284955706:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4261 = 236604284955706 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4261 = (12261:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4261
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4262) ≤ val WuPaper.ClassicalFourthData.Bq 4262
    have hp : val WuPaper.ClassicalFourthData.Bq 4262 = (236624474915897:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4262 = 236624474915897 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4262 = (6131:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4262
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4263) ≤ val WuPaper.ClassicalFourthData.Bq 4263
    have hp : val WuPaper.ClassicalFourthData.Bq 4263 = (236644656804749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4263 = 236644656804749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4263 = (12263:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4263
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4264) ≤ val WuPaper.ClassicalFourthData.Bq 4264
    have hp : val WuPaper.ClassicalFourthData.Bq 4264 = (236664830625391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4264 = 236664830625391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4264 = (1533:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4264
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4265) ≤ val WuPaper.ClassicalFourthData.Bq 4265
    have hp : val WuPaper.ClassicalFourthData.Bq 4265 = (236684996380953:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4265 = 236684996380953 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4265 = (2453:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4265
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4266) ≤ val WuPaper.ClassicalFourthData.Bq 4266
    have hp : val WuPaper.ClassicalFourthData.Bq 4266 = (236705154074564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4266 = 236705154074564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4266 = (6133:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4266
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4267) ≤ val WuPaper.ClassicalFourthData.Bq 4267
    have hp : val WuPaper.ClassicalFourthData.Bq 4267 = (236725303709350:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4267 = 236725303709350 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4267 = (12267:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4267
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4268) ≤ val WuPaper.ClassicalFourthData.Bq 4268
    have hp : val WuPaper.ClassicalFourthData.Bq 4268 = (236745445288436:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4268 = 236745445288436 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4268 = (3067:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4268
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4269) ≤ val WuPaper.ClassicalFourthData.Bq 4269
    have hp : val WuPaper.ClassicalFourthData.Bq 4269 = (236765578814945:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4269 = 236765578814945 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4269 = (12269:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4269
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4270) ≤ val WuPaper.ClassicalFourthData.Bq 4270
    have hp : val WuPaper.ClassicalFourthData.Bq 4270 = (236785704292000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4270 = 236785704292000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4270 = (1227:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4270
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4271) ≤ val WuPaper.ClassicalFourthData.Bq 4271
    have hp : val WuPaper.ClassicalFourthData.Bq 4271 = (236805821722722:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4271 = 236805821722722 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4271 = (12271:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4271
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_266
