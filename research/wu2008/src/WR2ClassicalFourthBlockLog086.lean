import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints086
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_086 (j : Fin 16) (hj : 16*86+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*86+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*86+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1376) ≤ val WuPaper.ClassicalFourthData.Bq 1376
    have hp : val WuPaper.ClassicalFourthData.Bq 1376 = (126130649360477:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1376 = 126130649360477 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1376 = (293:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1376
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1377) ≤ val WuPaper.ClassicalFourthData.Bq 1377
    have hp : val WuPaper.ClassicalFourthData.Bq 1377 = (126196539066930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1377 = 126196539066930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1377 = (9377:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1377
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1378) ≤ val WuPaper.ClassicalFourthData.Bq 1378
    have hp : val WuPaper.ClassicalFourthData.Bq 1378 = (126262399968771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1378 = 126262399968771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1378 = (4689:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1378
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1379) ≤ val WuPaper.ClassicalFourthData.Bq 1379
    have hp : val WuPaper.ClassicalFourthData.Bq 1379 = (126328232080698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1379 = 126328232080698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1379 = (9379:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1379
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1380) ≤ val WuPaper.ClassicalFourthData.Bq 1380
    have hp : val WuPaper.ClassicalFourthData.Bq 1380 = (126394035417400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1380 = 126394035417400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1380 = (469:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1380
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1381) ≤ val WuPaper.ClassicalFourthData.Bq 1381
    have hp : val WuPaper.ClassicalFourthData.Bq 1381 = (126459809993559:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1381 = 126459809993559 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1381 = (9381:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1381
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1382) ≤ val WuPaper.ClassicalFourthData.Bq 1382
    have hp : val WuPaper.ClassicalFourthData.Bq 1382 = (126525555823843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1382 = 126525555823843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1382 = (4691:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1382
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1383) ≤ val WuPaper.ClassicalFourthData.Bq 1383
    have hp : val WuPaper.ClassicalFourthData.Bq 1383 = (126591272922916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1383 = 126591272922916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1383 = (9383:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1383
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1384) ≤ val WuPaper.ClassicalFourthData.Bq 1384
    have hp : val WuPaper.ClassicalFourthData.Bq 1384 = (126656961305429:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1384 = 126656961305429 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1384 = (1173:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1384
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1385) ≤ val WuPaper.ClassicalFourthData.Bq 1385
    have hp : val WuPaper.ClassicalFourthData.Bq 1385 = (126722620986026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1385 = 126722620986026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1385 = (1877:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1385
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1386) ≤ val WuPaper.ClassicalFourthData.Bq 1386
    have hp : val WuPaper.ClassicalFourthData.Bq 1386 = (126788251979338:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1386 = 126788251979338 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1386 = (4693:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1386
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1387) ≤ val WuPaper.ClassicalFourthData.Bq 1387
    have hp : val WuPaper.ClassicalFourthData.Bq 1387 = (126853854299992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1387 = 126853854299992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1387 = (9387:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1387
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1388) ≤ val WuPaper.ClassicalFourthData.Bq 1388
    have hp : val WuPaper.ClassicalFourthData.Bq 1388 = (126919427962603:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1388 = 126919427962603 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1388 = (2347:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1388
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1389) ≤ val WuPaper.ClassicalFourthData.Bq 1389
    have hp : val WuPaper.ClassicalFourthData.Bq 1389 = (126984972981775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1389 = 126984972981775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1389 = (9389:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1389
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1390) ≤ val WuPaper.ClassicalFourthData.Bq 1390
    have hp : val WuPaper.ClassicalFourthData.Bq 1390 = (127050489372105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1390 = 127050489372105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1390 = (939:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1390
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1391) ≤ val WuPaper.ClassicalFourthData.Bq 1391
    have hp : val WuPaper.ClassicalFourthData.Bq 1391 = (127115977148181:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1391 = 127115977148181 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1391 = (9391:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1391
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_086
