import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints397
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_397 (j : Fin 16) (hj : 16*397+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*397+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*397+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6352) ≤ val WuPaper.ClassicalFourthData.Bq 6352
    have hp : val WuPaper.ClassicalFourthData.Bq 6352 = (265018220913796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6352 = 265018220913796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6352 = (897:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6352
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6353) ≤ val WuPaper.ClassicalFourthData.Bq 6353
    have hp : val WuPaper.ClassicalFourthData.Bq 6353 = (265026676420019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6353 = 265026676420019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6353 = (14353:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6353
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6354) ≤ val WuPaper.ClassicalFourthData.Bq 6354
    have hp : val WuPaper.ClassicalFourthData.Bq 6354 = (265035128148214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6354 = 265035128148214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6354 = (7177:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6354
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6355) ≤ val WuPaper.ClassicalFourthData.Bq 6355
    have hp : val WuPaper.ClassicalFourthData.Bq 6355 = (265043576099674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6355 = 265043576099674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6355 = (2871:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6355
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6356) ≤ val WuPaper.ClassicalFourthData.Bq 6356
    have hp : val WuPaper.ClassicalFourthData.Bq 6356 = (265052020275689:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6356 = 265052020275689 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6356 = (3589:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6356
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6357) ≤ val WuPaper.ClassicalFourthData.Bq 6357
    have hp : val WuPaper.ClassicalFourthData.Bq 6357 = (265060460677551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6357 = 265060460677551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6357 = (14357:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6357
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6358) ≤ val WuPaper.ClassicalFourthData.Bq 6358
    have hp : val WuPaper.ClassicalFourthData.Bq 6358 = (265068897306549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6358 = 265068897306549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6358 = (7179:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6358
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6359) ≤ val WuPaper.ClassicalFourthData.Bq 6359
    have hp : val WuPaper.ClassicalFourthData.Bq 6359 = (265077330163973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6359 = 265077330163973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6359 = (14359:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6359
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6360) ≤ val WuPaper.ClassicalFourthData.Bq 6360
    have hp : val WuPaper.ClassicalFourthData.Bq 6360 = (265085759251113:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6360 = 265085759251113 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6360 = (359:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6360
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6361) ≤ val WuPaper.ClassicalFourthData.Bq 6361
    have hp : val WuPaper.ClassicalFourthData.Bq 6361 = (265094184569256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6361 = 265094184569256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6361 = (14361:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6361
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6362) ≤ val WuPaper.ClassicalFourthData.Bq 6362
    have hp : val WuPaper.ClassicalFourthData.Bq 6362 = (265102606119692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6362 = 265102606119692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6362 = (7181:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6362
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6363) ≤ val WuPaper.ClassicalFourthData.Bq 6363
    have hp : val WuPaper.ClassicalFourthData.Bq 6363 = (265111023903708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6363 = 265111023903708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6363 = (14363:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6363
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6364) ≤ val WuPaper.ClassicalFourthData.Bq 6364
    have hp : val WuPaper.ClassicalFourthData.Bq 6364 = (265119437922590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6364 = 265119437922590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6364 = (3591:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6364
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6365) ≤ val WuPaper.ClassicalFourthData.Bq 6365
    have hp : val WuPaper.ClassicalFourthData.Bq 6365 = (265127848177627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6365 = 265127848177627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6365 = (2873:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6365
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6366) ≤ val WuPaper.ClassicalFourthData.Bq 6366
    have hp : val WuPaper.ClassicalFourthData.Bq 6366 = (265136254670103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6366 = 265136254670103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6366 = (7183:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6366
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6367) ≤ val WuPaper.ClassicalFourthData.Bq 6367
    have hp : val WuPaper.ClassicalFourthData.Bq 6367 = (265144657401304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6367 = 265144657401304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6367 = (14367:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6367
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_397
