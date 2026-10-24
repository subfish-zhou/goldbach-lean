import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints271
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_271 (j : Fin 16) (hj : 16*271+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*271+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*271+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4336) ≤ val WuPaper.ClassicalFourthData.Bq 4336
    have hp : val WuPaper.ClassicalFourthData.Bq 4336 = (238096343674164:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4336 = 238096343674164 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4336 = (771:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4336
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4337) ≤ val WuPaper.ClassicalFourthData.Bq 4337
    have hp : val WuPaper.ClassicalFourthData.Bq 4337 = (238115936875606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4337 = 238115936875606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4337 = (12337:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4337
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4338) ≤ val WuPaper.ClassicalFourthData.Bq 4338
    have hp : val WuPaper.ClassicalFourthData.Bq 4338 = (238135522236575:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4338 = 238135522236575 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4338 = (6169:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4338
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4339) ≤ val WuPaper.ClassicalFourthData.Bq 4339
    have hp : val WuPaper.ClassicalFourthData.Bq 4339 = (238155099760097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4339 = 238155099760097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4339 = (12339:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4339
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4340) ≤ val WuPaper.ClassicalFourthData.Bq 4340
    have hp : val WuPaper.ClassicalFourthData.Bq 4340 = (238174669449195:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4340 = 238174669449195 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4340 = (617:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4340
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4341) ≤ val WuPaper.ClassicalFourthData.Bq 4341
    have hp : val WuPaper.ClassicalFourthData.Bq 4341 = (238194231306891:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4341 = 238194231306891 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4341 = (12341:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4341
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4342) ≤ val WuPaper.ClassicalFourthData.Bq 4342
    have hp : val WuPaper.ClassicalFourthData.Bq 4342 = (238213785336206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4342 = 238213785336206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4342 = (6171:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4342
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4343) ≤ val WuPaper.ClassicalFourthData.Bq 4343
    have hp : val WuPaper.ClassicalFourthData.Bq 4343 = (238233331540160:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4343 = 238233331540160 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4343 = (12343:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4343
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4344) ≤ val WuPaper.ClassicalFourthData.Bq 4344
    have hp : val WuPaper.ClassicalFourthData.Bq 4344 = (238252869921770:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4344 = 238252869921770 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4344 = (1543:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4344
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4345) ≤ val WuPaper.ClassicalFourthData.Bq 4345
    have hp : val WuPaper.ClassicalFourthData.Bq 4345 = (238272400484053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4345 = 238272400484053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4345 = (2469:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4345
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4346) ≤ val WuPaper.ClassicalFourthData.Bq 4346
    have hp : val WuPaper.ClassicalFourthData.Bq 4346 = (238291923230025:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4346 = 238291923230025 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4346 = (6173:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4346
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4347) ≤ val WuPaper.ClassicalFourthData.Bq 4347
    have hp : val WuPaper.ClassicalFourthData.Bq 4347 = (238311438162699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4347 = 238311438162699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4347 = (12347:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4347
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4348) ≤ val WuPaper.ClassicalFourthData.Bq 4348
    have hp : val WuPaper.ClassicalFourthData.Bq 4348 = (238330945285088:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4348 = 238330945285088 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4348 = (3087:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4348
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4349) ≤ val WuPaper.ClassicalFourthData.Bq 4349
    have hp : val WuPaper.ClassicalFourthData.Bq 4349 = (238350444600202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4349 = 238350444600202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4349 = (12349:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4349
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4350) ≤ val WuPaper.ClassicalFourthData.Bq 4350
    have hp : val WuPaper.ClassicalFourthData.Bq 4350 = (238369936111053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4350 = 238369936111053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4350 = (247:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4350
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4351) ≤ val WuPaper.ClassicalFourthData.Bq 4351
    have hp : val WuPaper.ClassicalFourthData.Bq 4351 = (238389419820647:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4351 = 238389419820647 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4351 = (12351:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4351
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_271
