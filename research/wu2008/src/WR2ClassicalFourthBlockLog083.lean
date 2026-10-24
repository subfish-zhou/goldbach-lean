import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints083
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_083 (j : Fin 16) (hj : 16*83+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*83+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*83+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1328) ≤ val WuPaper.ClassicalFourthData.Bq 1328
    have hp : val WuPaper.ClassicalFourthData.Bq 1328 = (122933778781389:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1328 = 122933778781389 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1328 = (583:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1328
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1329) ≤ val WuPaper.ClassicalFourthData.Bq 1329
    have hp : val WuPaper.ClassicalFourthData.Bq 1329 = (123001068579593:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1329 = 123001068579593 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1329 = (9329:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1329
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1330) ≤ val WuPaper.ClassicalFourthData.Bq 1330
    have hp : val WuPaper.ClassicalFourthData.Bq 1330 = (123068328856533:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1330 = 123068328856533 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1330 = (933:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1330
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1331) ≤ val WuPaper.ClassicalFourthData.Bq 1331
    have hp : val WuPaper.ClassicalFourthData.Bq 1331 = (123135559627364:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1331 = 123135559627364 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1331 = (9331:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1331
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1332) ≤ val WuPaper.ClassicalFourthData.Bq 1332
    have hp : val WuPaper.ClassicalFourthData.Bq 1332 = (123202760907232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1332 = 123202760907232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1332 = (2333:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1332
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1333) ≤ val WuPaper.ClassicalFourthData.Bq 1333
    have hp : val WuPaper.ClassicalFourthData.Bq 1333 = (123269932711272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1333 = 123269932711272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1333 = (9333:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1333
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1334) ≤ val WuPaper.ClassicalFourthData.Bq 1334
    have hp : val WuPaper.ClassicalFourthData.Bq 1334 = (123337075054610:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1334 = 123337075054610 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1334 = (4667:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1334
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1335) ≤ val WuPaper.ClassicalFourthData.Bq 1335
    have hp : val WuPaper.ClassicalFourthData.Bq 1335 = (123404187952363:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1335 = 123404187952363 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1335 = (1867:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1335
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1336) ≤ val WuPaper.ClassicalFourthData.Bq 1336
    have hp : val WuPaper.ClassicalFourthData.Bq 1336 = (123471271419637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1336 = 123471271419637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1336 = (1167:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1336
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1337) ≤ val WuPaper.ClassicalFourthData.Bq 1337
    have hp : val WuPaper.ClassicalFourthData.Bq 1337 = (123538325471530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1337 = 123538325471530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1337 = (9337:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1337
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1338) ≤ val WuPaper.ClassicalFourthData.Bq 1338
    have hp : val WuPaper.ClassicalFourthData.Bq 1338 = (123605350123128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1338 = 123605350123128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1338 = (4669:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1338
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1339) ≤ val WuPaper.ClassicalFourthData.Bq 1339
    have hp : val WuPaper.ClassicalFourthData.Bq 1339 = (123672345389511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1339 = 123672345389511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1339 = (9339:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1339
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1340) ≤ val WuPaper.ClassicalFourthData.Bq 1340
    have hp : val WuPaper.ClassicalFourthData.Bq 1340 = (123739311285745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1340 = 123739311285745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1340 = (467:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1340
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1341) ≤ val WuPaper.ClassicalFourthData.Bq 1341
    have hp : val WuPaper.ClassicalFourthData.Bq 1341 = (123806247826890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1341 = 123806247826890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1341 = (9341:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1341
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1342) ≤ val WuPaper.ClassicalFourthData.Bq 1342
    have hp : val WuPaper.ClassicalFourthData.Bq 1342 = (123873155027994:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1342 = 123873155027994 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1342 = (4671:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1342
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1343) ≤ val WuPaper.ClassicalFourthData.Bq 1343
    have hp : val WuPaper.ClassicalFourthData.Bq 1343 = (123940032904097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1343 = 123940032904097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1343 = (9343:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_083
