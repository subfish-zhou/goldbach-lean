import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints584
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_584 (j : Fin 16) (hj : 16*584+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*584+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*584+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9344) ≤ val WuPaper.ClassicalFourthData.Bq 9344
    have hp : val WuPaper.ClassicalFourthData.Bq 9344 = (277853432778855:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9344 = 277853432778855 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9344 = (542:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9344
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9345) ≤ val WuPaper.ClassicalFourthData.Bq 9345
    have hp : val WuPaper.ClassicalFourthData.Bq 9345 = (277854695132723:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9345 = 277854695132723 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9345 = (3469:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9345
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9346) ≤ val WuPaper.ClassicalFourthData.Bq 9346
    have hp : val WuPaper.ClassicalFourthData.Bq 9346 = (277855956046178:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9346 = 277855956046178 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9346 = (8673:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9346
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9347) ≤ val WuPaper.ClassicalFourthData.Bq 9347
    have hp : val WuPaper.ClassicalFourthData.Bq 9347 = (277857215519665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9347 = 277857215519665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9347 = (17347:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9347
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9348) ≤ val WuPaper.ClassicalFourthData.Bq 9348
    have hp : val WuPaper.ClassicalFourthData.Bq 9348 = (277858473553626:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9348 = 277858473553626 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9348 = (4337:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9348
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9349) ≤ val WuPaper.ClassicalFourthData.Bq 9349
    have hp : val WuPaper.ClassicalFourthData.Bq 9349 = (277859730148504:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9349 = 277859730148504 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9349 = (17349:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9349
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9350) ≤ val WuPaper.ClassicalFourthData.Bq 9350
    have hp : val WuPaper.ClassicalFourthData.Bq 9350 = (277860985304742:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9350 = 277860985304742 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9350 = (347:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9350
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9351) ≤ val WuPaper.ClassicalFourthData.Bq 9351
    have hp : val WuPaper.ClassicalFourthData.Bq 9351 = (277862239022783:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9351 = 277862239022783 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9351 = (17351:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9351
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9352) ≤ val WuPaper.ClassicalFourthData.Bq 9352
    have hp : val WuPaper.ClassicalFourthData.Bq 9352 = (277863491303068:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9352 = 277863491303068 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9352 = (2169:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9352
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9353) ≤ val WuPaper.ClassicalFourthData.Bq 9353
    have hp : val WuPaper.ClassicalFourthData.Bq 9353 = (277864742146040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9353 = 277864742146040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9353 = (17353:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9353
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9354) ≤ val WuPaper.ClassicalFourthData.Bq 9354
    have hp : val WuPaper.ClassicalFourthData.Bq 9354 = (277865991552141:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9354 = 277865991552141 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9354 = (8677:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9354
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9355) ≤ val WuPaper.ClassicalFourthData.Bq 9355
    have hp : val WuPaper.ClassicalFourthData.Bq 9355 = (277867239521814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9355 = 277867239521814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9355 = (3471:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9355
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9356) ≤ val WuPaper.ClassicalFourthData.Bq 9356
    have hp : val WuPaper.ClassicalFourthData.Bq 9356 = (277868486055499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9356 = 277868486055499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9356 = (4339:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9356
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9357) ≤ val WuPaper.ClassicalFourthData.Bq 9357
    have hp : val WuPaper.ClassicalFourthData.Bq 9357 = (277869731153639:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9357 = 277869731153639 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9357 = (17357:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9357
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9358) ≤ val WuPaper.ClassicalFourthData.Bq 9358
    have hp : val WuPaper.ClassicalFourthData.Bq 9358 = (277870974816675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9358 = 277870974816675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9358 = (8679:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9358
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9359) ≤ val WuPaper.ClassicalFourthData.Bq 9359
    have hp : val WuPaper.ClassicalFourthData.Bq 9359 = (277872217045048:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9359 = 277872217045048 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9359 = (17359:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9359
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_584
