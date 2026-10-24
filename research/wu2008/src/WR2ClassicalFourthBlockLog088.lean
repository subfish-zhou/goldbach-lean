import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints088
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_088 (j : Fin 16) (hj : 16*88+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*88+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*88+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1408) ≤ val WuPaper.ClassicalFourthData.Bq 1408
    have hp : val WuPaper.ClassicalFourthData.Bq 1408 = (128224905451009:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1408 = 128224905451009 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1408 = (294:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1408
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1409) ≤ val WuPaper.ClassicalFourthData.Bq 1409
    have hp : val WuPaper.ClassicalFourthData.Bq 1409 = (128289880654437:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1409 = 128289880654437 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1409 = (9409:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1409
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1410) ≤ val WuPaper.ClassicalFourthData.Bq 1410
    have hp : val WuPaper.ClassicalFourthData.Bq 1410 = (128354827519023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1410 = 128354827519023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1410 = (941:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1410
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1411) ≤ val WuPaper.ClassicalFourthData.Bq 1411
    have hp : val WuPaper.ClassicalFourthData.Bq 1411 = (128419746059169:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1411 = 128419746059169 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1411 = (9411:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1411
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1412) ≤ val WuPaper.ClassicalFourthData.Bq 1412
    have hp : val WuPaper.ClassicalFourthData.Bq 1412 = (128484636289270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1412 = 128484636289270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1412 = (2353:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1412
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1413) ≤ val WuPaper.ClassicalFourthData.Bq 1413
    have hp : val WuPaper.ClassicalFourthData.Bq 1413 = (128549498223712:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1413 = 128549498223712 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1413 = (9413:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1413
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1414) ≤ val WuPaper.ClassicalFourthData.Bq 1414
    have hp : val WuPaper.ClassicalFourthData.Bq 1414 = (128614331876873:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1414 = 128614331876873 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1414 = (4707:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1414
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1415) ≤ val WuPaper.ClassicalFourthData.Bq 1415
    have hp : val WuPaper.ClassicalFourthData.Bq 1415 = (128679137263118:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1415 = 128679137263118 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1415 = (1883:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1415
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1416) ≤ val WuPaper.ClassicalFourthData.Bq 1416
    have hp : val WuPaper.ClassicalFourthData.Bq 1416 = (128743914396807:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1416 = 128743914396807 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1416 = (1177:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1416
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1417) ≤ val WuPaper.ClassicalFourthData.Bq 1417
    have hp : val WuPaper.ClassicalFourthData.Bq 1417 = (128808663292289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1417 = 128808663292289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1417 = (9417:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1417
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1418) ≤ val WuPaper.ClassicalFourthData.Bq 1418
    have hp : val WuPaper.ClassicalFourthData.Bq 1418 = (128873383963905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1418 = 128873383963905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1418 = (4709:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1418
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1419) ≤ val WuPaper.ClassicalFourthData.Bq 1419
    have hp : val WuPaper.ClassicalFourthData.Bq 1419 = (128938076425985:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1419 = 128938076425985 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1419 = (9419:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1419
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1420) ≤ val WuPaper.ClassicalFourthData.Bq 1420
    have hp : val WuPaper.ClassicalFourthData.Bq 1420 = (129002740692852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1420 = 129002740692852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1420 = (471:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1420
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1421) ≤ val WuPaper.ClassicalFourthData.Bq 1421
    have hp : val WuPaper.ClassicalFourthData.Bq 1421 = (129067376778818:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1421 = 129067376778818 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1421 = (9421:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1421
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1422) ≤ val WuPaper.ClassicalFourthData.Bq 1422
    have hp : val WuPaper.ClassicalFourthData.Bq 1422 = (129131984698189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1422 = 129131984698189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1422 = (4711:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1422
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1423) ≤ val WuPaper.ClassicalFourthData.Bq 1423
    have hp : val WuPaper.ClassicalFourthData.Bq 1423 = (129196564465259:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1423 = 129196564465259 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1423 = (9423:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1423
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_088
