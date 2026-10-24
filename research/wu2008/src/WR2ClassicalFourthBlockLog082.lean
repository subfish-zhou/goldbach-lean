import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints082
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_082 (j : Fin 16) (hj : 16*82+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*82+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*82+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1312) ≤ val WuPaper.ClassicalFourthData.Bq 1312
    have hp : val WuPaper.ClassicalFourthData.Bq 1312 = (121853114714022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1312 = 121853114714022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1312 = (291:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1312
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1313) ≤ val WuPaper.ClassicalFourthData.Bq 1313
    have hp : val WuPaper.ClassicalFourthData.Bq 1313 = (121920878921472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1313 = 121920878921472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1313 = (9313:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1313
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1314) ≤ val WuPaper.ClassicalFourthData.Bq 1314
    have hp : val WuPaper.ClassicalFourthData.Bq 1314 = (121988613363853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1314 = 121988613363853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1314 = (4657:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1314
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1315) ≤ val WuPaper.ClassicalFourthData.Bq 1315
    have hp : val WuPaper.ClassicalFourthData.Bq 1315 = (122056318056477:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1315 = 122056318056477 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1315 = (1863:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1315
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1316) ≤ val WuPaper.ClassicalFourthData.Bq 1316
    have hp : val WuPaper.ClassicalFourthData.Bq 1316 = (122123993014646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1316 = 122123993014646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1316 = (2329:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1316
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1317) ≤ val WuPaper.ClassicalFourthData.Bq 1317
    have hp : val WuPaper.ClassicalFourthData.Bq 1317 = (122191638253649:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1317 = 122191638253649 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1317 = (9317:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1317
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1318) ≤ val WuPaper.ClassicalFourthData.Bq 1318
    have hp : val WuPaper.ClassicalFourthData.Bq 1318 = (122259253788770:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1318 = 122259253788770 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1318 = (4659:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1318
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1319) ≤ val WuPaper.ClassicalFourthData.Bq 1319
    have hp : val WuPaper.ClassicalFourthData.Bq 1319 = (122326839635279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1319 = 122326839635279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1319 = (9319:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1319
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1320) ≤ val WuPaper.ClassicalFourthData.Bq 1320
    have hp : val WuPaper.ClassicalFourthData.Bq 1320 = (122394395808439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1320 = 122394395808439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1320 = (233:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1320
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1321) ≤ val WuPaper.ClassicalFourthData.Bq 1321
    have hp : val WuPaper.ClassicalFourthData.Bq 1321 = (122461922323503:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1321 = 122461922323503 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1321 = (9321:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1321
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1322) ≤ val WuPaper.ClassicalFourthData.Bq 1322
    have hp : val WuPaper.ClassicalFourthData.Bq 1322 = (122529419195713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1322 = 122529419195713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1322 = (4661:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1322
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1323) ≤ val WuPaper.ClassicalFourthData.Bq 1323
    have hp : val WuPaper.ClassicalFourthData.Bq 1323 = (122596886440301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1323 = 122596886440301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1323 = (9323:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1323
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1324) ≤ val WuPaper.ClassicalFourthData.Bq 1324
    have hp : val WuPaper.ClassicalFourthData.Bq 1324 = (122664324072491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1324 = 122664324072491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1324 = (2331:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1324
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1325) ≤ val WuPaper.ClassicalFourthData.Bq 1325
    have hp : val WuPaper.ClassicalFourthData.Bq 1325 = (122731732107496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1325 = 122731732107496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1325 = (373:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1325
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1326) ≤ val WuPaper.ClassicalFourthData.Bq 1326
    have hp : val WuPaper.ClassicalFourthData.Bq 1326 = (122799110560519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1326 = 122799110560519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1326 = (4663:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1326
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1327) ≤ val WuPaper.ClassicalFourthData.Bq 1327
    have hp : val WuPaper.ClassicalFourthData.Bq 1327 = (122866459446756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1327 = 122866459446756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1327 = (9327:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1327
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_082
