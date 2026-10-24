import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints520
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_520 (j : Fin 16) (hj : 16*520+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*520+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*520+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8320) ≤ val WuPaper.ClassicalFourthData.Bq 8320
    have hp : val WuPaper.ClassicalFourthData.Bq 8320 = (275718038478039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8320 = 275718038478039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8320 = (102:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8320
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8321) ≤ val WuPaper.ClassicalFourthData.Bq 8321
    have hp : val WuPaper.ClassicalFourthData.Bq 8321 = (275721037320646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8321 = 275721037320646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8321 = (16321:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8321
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8322) ≤ val WuPaper.ClassicalFourthData.Bq 8322
    have hp : val WuPaper.ClassicalFourthData.Bq 8322 = (275724034181455:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8322 = 275724034181455 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8322 = (8161:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8322
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8323) ≤ val WuPaper.ClassicalFourthData.Bq 8323
    have hp : val WuPaper.ClassicalFourthData.Bq 8323 = (275727029061090:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8323 = 275727029061090 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8323 = (16323:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8323
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8324) ≤ val WuPaper.ClassicalFourthData.Bq 8324
    have hp : val WuPaper.ClassicalFourthData.Bq 8324 = (275730021960178:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8324 = 275730021960178 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8324 = (4081:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8324
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8325) ≤ val WuPaper.ClassicalFourthData.Bq 8325
    have hp : val WuPaper.ClassicalFourthData.Bq 8325 = (275733012879346:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8325 = 275733012879346 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8325 = (653:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8325
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8326) ≤ val WuPaper.ClassicalFourthData.Bq 8326
    have hp : val WuPaper.ClassicalFourthData.Bq 8326 = (275736001819218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8326 = 275736001819218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8326 = (8163:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8326
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8327) ≤ val WuPaper.ClassicalFourthData.Bq 8327
    have hp : val WuPaper.ClassicalFourthData.Bq 8327 = (275738988780420:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8327 = 275738988780420 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8327 = (16327:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8327
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8328) ≤ val WuPaper.ClassicalFourthData.Bq 8328
    have hp : val WuPaper.ClassicalFourthData.Bq 8328 = (275741973763577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8328 = 275741973763577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8328 = (2041:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8328
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8329) ≤ val WuPaper.ClassicalFourthData.Bq 8329
    have hp : val WuPaper.ClassicalFourthData.Bq 8329 = (275744956769314:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8329 = 275744956769314 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8329 = (16329:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8329
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8330) ≤ val WuPaper.ClassicalFourthData.Bq 8330
    have hp : val WuPaper.ClassicalFourthData.Bq 8330 = (275747937798256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8330 = 275747937798256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8330 = (1633:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8330
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8331) ≤ val WuPaper.ClassicalFourthData.Bq 8331
    have hp : val WuPaper.ClassicalFourthData.Bq 8331 = (275750916851027:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8331 = 275750916851027 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8331 = (16331:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8331
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8332) ≤ val WuPaper.ClassicalFourthData.Bq 8332
    have hp : val WuPaper.ClassicalFourthData.Bq 8332 = (275753893928251:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8332 = 275753893928251 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8332 = (4083:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8332
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8333) ≤ val WuPaper.ClassicalFourthData.Bq 8333
    have hp : val WuPaper.ClassicalFourthData.Bq 8333 = (275756869030553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8333 = 275756869030553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8333 = (16333:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8333
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8334) ≤ val WuPaper.ClassicalFourthData.Bq 8334
    have hp : val WuPaper.ClassicalFourthData.Bq 8334 = (275759842158557:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8334 = 275759842158557 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8334 = (8167:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8334
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8335) ≤ val WuPaper.ClassicalFourthData.Bq 8335
    have hp : val WuPaper.ClassicalFourthData.Bq 8335 = (275762813312885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8335 = 275762813312885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8335 = (3267:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8335
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_520
