import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints273
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_273 (j : Fin 16) (hj : 16*273+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*273+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*273+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4368) ≤ val WuPaper.ClassicalFourthData.Bq 4368
    have hp : val WuPaper.ClassicalFourthData.Bq 4368 = (238719452200090:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4368 = 238719452200090 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4368 = (773:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4368
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4369) ≤ val WuPaper.ClassicalFourthData.Bq 4369
    have hp : val WuPaper.ClassicalFourthData.Bq 4369 = (238738795999951:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4369 = 238738795999951 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4369 = (12369:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4369
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4370) ≤ val WuPaper.ClassicalFourthData.Bq 4370
    have hp : val WuPaper.ClassicalFourthData.Bq 4370 = (238758132055455:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4370 = 238758132055455 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4370 = (1237:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4370
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4371) ≤ val WuPaper.ClassicalFourthData.Bq 4371
    have hp : val WuPaper.ClassicalFourthData.Bq 4371 = (238777460369584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4371 = 238777460369584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4371 = (12371:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4371
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4372) ≤ val WuPaper.ClassicalFourthData.Bq 4372
    have hp : val WuPaper.ClassicalFourthData.Bq 4372 = (238796780945317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4372 = 238796780945317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4372 = (3093:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4372
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4373) ≤ val WuPaper.ClassicalFourthData.Bq 4373
    have hp : val WuPaper.ClassicalFourthData.Bq 4373 = (238816093785632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4373 = 238816093785632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4373 = (12373:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4373
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4374) ≤ val WuPaper.ClassicalFourthData.Bq 4374
    have hp : val WuPaper.ClassicalFourthData.Bq 4374 = (238835398893507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4374 = 238835398893507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4374 = (6187:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4374
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4375) ≤ val WuPaper.ClassicalFourthData.Bq 4375
    have hp : val WuPaper.ClassicalFourthData.Bq 4375 = (238854696271916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4375 = 238854696271916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4375 = (99:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4375
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4376) ≤ val WuPaper.ClassicalFourthData.Bq 4376
    have hp : val WuPaper.ClassicalFourthData.Bq 4376 = (238873985923835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4376 = 238873985923835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4376 = (1547:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4376
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4377) ≤ val WuPaper.ClassicalFourthData.Bq 4377
    have hp : val WuPaper.ClassicalFourthData.Bq 4377 = (238893267852237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4377 = 238893267852237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4377 = (12377:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4377
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4378) ≤ val WuPaper.ClassicalFourthData.Bq 4378
    have hp : val WuPaper.ClassicalFourthData.Bq 4378 = (238912542060092:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4378 = 238912542060092 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4378 = (6189:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4378
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4379) ≤ val WuPaper.ClassicalFourthData.Bq 4379
    have hp : val WuPaper.ClassicalFourthData.Bq 4379 = (238931808550371:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4379 = 238931808550371 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4379 = (12379:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4379
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4380) ≤ val WuPaper.ClassicalFourthData.Bq 4380
    have hp : val WuPaper.ClassicalFourthData.Bq 4380 = (238951067326043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4380 = 238951067326043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4380 = (619:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4380
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4381) ≤ val WuPaper.ClassicalFourthData.Bq 4381
    have hp : val WuPaper.ClassicalFourthData.Bq 4381 = (238970318390075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4381 = 238970318390075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4381 = (12381:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4381
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4382) ≤ val WuPaper.ClassicalFourthData.Bq 4382
    have hp : val WuPaper.ClassicalFourthData.Bq 4382 = (238989561745434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4382 = 238989561745434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4382 = (6191:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4382
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4383) ≤ val WuPaper.ClassicalFourthData.Bq 4383
    have hp : val WuPaper.ClassicalFourthData.Bq 4383 = (239008797395084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4383 = 239008797395084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4383 = (12383:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_273
