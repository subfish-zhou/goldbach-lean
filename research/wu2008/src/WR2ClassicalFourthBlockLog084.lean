import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints084
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_084 (j : Fin 16) (hj : 16*84+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*84+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*84+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1344) ≤ val WuPaper.ClassicalFourthData.Bq 1344
    have hp : val WuPaper.ClassicalFourthData.Bq 1344 = (124006881470229:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1344 = 124006881470229 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1344 = (292:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1344
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1345) ≤ val WuPaper.ClassicalFourthData.Bq 1345
    have hp : val WuPaper.ClassicalFourthData.Bq 1345 = (124073700741410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1345 = 124073700741410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1345 = (1869:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1345
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1346) ≤ val WuPaper.ClassicalFourthData.Bq 1346
    have hp : val WuPaper.ClassicalFourthData.Bq 1346 = (124140490732650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1346 = 124140490732650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1346 = (4673:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1346
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1347) ≤ val WuPaper.ClassicalFourthData.Bq 1347
    have hp : val WuPaper.ClassicalFourthData.Bq 1347 = (124207251458952:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1347 = 124207251458952 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1347 = (9347:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1347
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1348) ≤ val WuPaper.ClassicalFourthData.Bq 1348
    have hp : val WuPaper.ClassicalFourthData.Bq 1348 = (124273982935305:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1348 = 124273982935305 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1348 = (2337:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1348
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1349) ≤ val WuPaper.ClassicalFourthData.Bq 1349
    have hp : val WuPaper.ClassicalFourthData.Bq 1349 = (124340685176692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1349 = 124340685176692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1349 = (9349:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1349
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1350) ≤ val WuPaper.ClassicalFourthData.Bq 1350
    have hp : val WuPaper.ClassicalFourthData.Bq 1350 = (124407358198086:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1350 = 124407358198086 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1350 = (187:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1350
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1351) ≤ val WuPaper.ClassicalFourthData.Bq 1351
    have hp : val WuPaper.ClassicalFourthData.Bq 1351 = (124474002014449:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1351 = 124474002014449 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1351 = (9351:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1351
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1352) ≤ val WuPaper.ClassicalFourthData.Bq 1352
    have hp : val WuPaper.ClassicalFourthData.Bq 1352 = (124540616640735:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1352 = 124540616640735 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1352 = (1169:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1352
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1353) ≤ val WuPaper.ClassicalFourthData.Bq 1353
    have hp : val WuPaper.ClassicalFourthData.Bq 1353 = (124607202091887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1353 = 124607202091887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1353 = (9353:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1353
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1354) ≤ val WuPaper.ClassicalFourthData.Bq 1354
    have hp : val WuPaper.ClassicalFourthData.Bq 1354 = (124673758382840:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1354 = 124673758382840 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1354 = (4677:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1354
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1355) ≤ val WuPaper.ClassicalFourthData.Bq 1355
    have hp : val WuPaper.ClassicalFourthData.Bq 1355 = (124740285528518:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1355 = 124740285528518 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1355 = (1871:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1355
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1356) ≤ val WuPaper.ClassicalFourthData.Bq 1356
    have hp : val WuPaper.ClassicalFourthData.Bq 1356 = (124806783543838:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1356 = 124806783543838 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1356 = (2339:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1356
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1357) ≤ val WuPaper.ClassicalFourthData.Bq 1357
    have hp : val WuPaper.ClassicalFourthData.Bq 1357 = (124873252443704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1357 = 124873252443704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1357 = (9357:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1357
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1358) ≤ val WuPaper.ClassicalFourthData.Bq 1358
    have hp : val WuPaper.ClassicalFourthData.Bq 1358 = (124939692243012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1358 = 124939692243012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1358 = (4679:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1358
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1359) ≤ val WuPaper.ClassicalFourthData.Bq 1359
    have hp : val WuPaper.ClassicalFourthData.Bq 1359 = (125006102956651:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1359 = 125006102956651 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1359 = (9359:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1359
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_084
