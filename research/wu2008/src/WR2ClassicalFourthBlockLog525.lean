import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints525
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_525 (j : Fin 16) (hj : 16*525+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*525+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*525+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8400) ≤ val WuPaper.ClassicalFourthData.Bq 8400
    have hp : val WuPaper.ClassicalFourthData.Bq 8400 = (275951734511430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8400 = 275951734511430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8400 = (41:ℝ)/10 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8400
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8401) ≤ val WuPaper.ClassicalFourthData.Bq 8401
    have hp : val WuPaper.ClassicalFourthData.Bq 8401 = (275954576771299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8401 = 275954576771299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8401 = (16401:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8401
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8402) ≤ val WuPaper.ClassicalFourthData.Bq 8402
    have hp : val WuPaper.ClassicalFourthData.Bq 8402 = (275957417098788:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8402 = 275957417098788 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8402 = (8201:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8402
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8403) ≤ val WuPaper.ClassicalFourthData.Bq 8403
    have hp : val WuPaper.ClassicalFourthData.Bq 8403 = (275960255494507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8403 = 275960255494507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8403 = (16403:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8403
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8404) ≤ val WuPaper.ClassicalFourthData.Bq 8404
    have hp : val WuPaper.ClassicalFourthData.Bq 8404 = (275963091959064:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8404 = 275963091959064 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8404 = (4101:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8404
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8405) ≤ val WuPaper.ClassicalFourthData.Bq 8405
    have hp : val WuPaper.ClassicalFourthData.Bq 8405 = (275965926493068:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8405 = 275965926493068 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8405 = (3281:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8405
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8406) ≤ val WuPaper.ClassicalFourthData.Bq 8406
    have hp : val WuPaper.ClassicalFourthData.Bq 8406 = (275968759097127:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8406 = 275968759097127 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8406 = (8203:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8406
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8407) ≤ val WuPaper.ClassicalFourthData.Bq 8407
    have hp : val WuPaper.ClassicalFourthData.Bq 8407 = (275971589771850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8407 = 275971589771850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8407 = (16407:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8407
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8408) ≤ val WuPaper.ClassicalFourthData.Bq 8408
    have hp : val WuPaper.ClassicalFourthData.Bq 8408 = (275974418517845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8408 = 275974418517845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8408 = (2051:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8408
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8409) ≤ val WuPaper.ClassicalFourthData.Bq 8409
    have hp : val WuPaper.ClassicalFourthData.Bq 8409 = (275977245335720:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8409 = 275977245335720 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8409 = (16409:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8409
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8410) ≤ val WuPaper.ClassicalFourthData.Bq 8410
    have hp : val WuPaper.ClassicalFourthData.Bq 8410 = (275980070226082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8410 = 275980070226082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8410 = (1641:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8410
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8411) ≤ val WuPaper.ClassicalFourthData.Bq 8411
    have hp : val WuPaper.ClassicalFourthData.Bq 8411 = (275982893189539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8411 = 275982893189539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8411 = (16411:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8411
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8412) ≤ val WuPaper.ClassicalFourthData.Bq 8412
    have hp : val WuPaper.ClassicalFourthData.Bq 8412 = (275985714226699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8412 = 275985714226699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8412 = (4103:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8412
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8413) ≤ val WuPaper.ClassicalFourthData.Bq 8413
    have hp : val WuPaper.ClassicalFourthData.Bq 8413 = (275988533338167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8413 = 275988533338167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8413 = (16413:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8413
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8414) ≤ val WuPaper.ClassicalFourthData.Bq 8414
    have hp : val WuPaper.ClassicalFourthData.Bq 8414 = (275991350524551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8414 = 275991350524551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8414 = (8207:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8414
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8415) ≤ val WuPaper.ClassicalFourthData.Bq 8415
    have hp : val WuPaper.ClassicalFourthData.Bq 8415 = (275994165786458:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8415 = 275994165786458 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8415 = (3283:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8415
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_525
