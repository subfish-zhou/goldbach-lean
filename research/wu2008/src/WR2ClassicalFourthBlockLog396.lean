import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints396
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_396 (j : Fin 16) (hj : 16*396+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*396+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*396+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6336) ≤ val WuPaper.ClassicalFourthData.Bq 6336
    have hp : val WuPaper.ClassicalFourthData.Bq 6336 = (264882417946540:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6336 = 264882417946540 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6336 = (448:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6336
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6337) ≤ val WuPaper.ClassicalFourthData.Bq 6337
    have hp : val WuPaper.ClassicalFourthData.Bq 6337 = (264890934077283:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6337 = 264890934077283 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6337 = (14337:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6337
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6338) ≤ val WuPaper.ClassicalFourthData.Bq 6338
    have hp : val WuPaper.ClassicalFourthData.Bq 6338 = (264899446409263:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6338 = 264899446409263 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6338 = (7169:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6338
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6339) ≤ val WuPaper.ClassicalFourthData.Bq 6339
    have hp : val WuPaper.ClassicalFourthData.Bq 6339 = (264907954943779:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6339 = 264907954943779 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6339 = (14339:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6339
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6340) ≤ val WuPaper.ClassicalFourthData.Bq 6340
    have hp : val WuPaper.ClassicalFourthData.Bq 6340 = (264916459682131:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6340 = 264916459682131 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6340 = (717:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6340
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6341) ≤ val WuPaper.ClassicalFourthData.Bq 6341
    have hp : val WuPaper.ClassicalFourthData.Bq 6341 = (264924960625617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6341 = 264924960625617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6341 = (14341:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6341
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6342) ≤ val WuPaper.ClassicalFourthData.Bq 6342
    have hp : val WuPaper.ClassicalFourthData.Bq 6342 = (264933457775536:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6342 = 264933457775536 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6342 = (7171:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6342
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6343) ≤ val WuPaper.ClassicalFourthData.Bq 6343
    have hp : val WuPaper.ClassicalFourthData.Bq 6343 = (264941951133186:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6343 = 264941951133186 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6343 = (14343:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6343
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6344) ≤ val WuPaper.ClassicalFourthData.Bq 6344
    have hp : val WuPaper.ClassicalFourthData.Bq 6344 = (264950440699864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6344 = 264950440699864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6344 = (1793:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6344
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6345) ≤ val WuPaper.ClassicalFourthData.Bq 6345
    have hp : val WuPaper.ClassicalFourthData.Bq 6345 = (264958926476866:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6345 = 264958926476866 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6345 = (2869:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6345
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6346) ≤ val WuPaper.ClassicalFourthData.Bq 6346
    have hp : val WuPaper.ClassicalFourthData.Bq 6346 = (264967408465490:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6346 = 264967408465490 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6346 = (7173:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6346
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6347) ≤ val WuPaper.ClassicalFourthData.Bq 6347
    have hp : val WuPaper.ClassicalFourthData.Bq 6347 = (264975886667030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6347 = 264975886667030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6347 = (14347:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6347
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6348) ≤ val WuPaper.ClassicalFourthData.Bq 6348
    have hp : val WuPaper.ClassicalFourthData.Bq 6348 = (264984361082782:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6348 = 264984361082782 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6348 = (3587:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6348
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6349) ≤ val WuPaper.ClassicalFourthData.Bq 6349
    have hp : val WuPaper.ClassicalFourthData.Bq 6349 = (264992831714041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6349 = 264992831714041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6349 = (14349:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6349
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6350) ≤ val WuPaper.ClassicalFourthData.Bq 6350
    have hp : val WuPaper.ClassicalFourthData.Bq 6350 = (265001298562100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6350 = 265001298562100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6350 = (287:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6350
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6351) ≤ val WuPaper.ClassicalFourthData.Bq 6351
    have hp : val WuPaper.ClassicalFourthData.Bq 6351 = (265009761628254:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6351 = 265009761628254 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6351 = (14351:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6351
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_396
