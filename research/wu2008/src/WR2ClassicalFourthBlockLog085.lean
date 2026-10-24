import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints085
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_085 (j : Fin 16) (hj : 16*85+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*85+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*85+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1360) ≤ val WuPaper.ClassicalFourthData.Bq 1360
    have hp : val WuPaper.ClassicalFourthData.Bq 1360 = (125072484599496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1360 = 125072484599496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1360 = (117:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1360
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1361) ≤ val WuPaper.ClassicalFourthData.Bq 1361
    have hp : val WuPaper.ClassicalFourthData.Bq 1361 = (125138837186417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1361 = 125138837186417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1361 = (9361:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1361
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1362) ≤ val WuPaper.ClassicalFourthData.Bq 1362
    have hp : val WuPaper.ClassicalFourthData.Bq 1362 = (125205160732270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1362 = 125205160732270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1362 = (4681:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1362
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1363) ≤ val WuPaper.ClassicalFourthData.Bq 1363
    have hp : val WuPaper.ClassicalFourthData.Bq 1363 = (125271455251906:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1363 = 125271455251906 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1363 = (9363:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1363
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1364) ≤ val WuPaper.ClassicalFourthData.Bq 1364
    have hp : val WuPaper.ClassicalFourthData.Bq 1364 = (125337720760163:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1364 = 125337720760163 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1364 = (2341:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1364
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1365) ≤ val WuPaper.ClassicalFourthData.Bq 1365
    have hp : val WuPaper.ClassicalFourthData.Bq 1365 = (125403957271873:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1365 = 125403957271873 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1365 = (1873:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1365
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1366) ≤ val WuPaper.ClassicalFourthData.Bq 1366
    have hp : val WuPaper.ClassicalFourthData.Bq 1366 = (125470164801855:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1366 = 125470164801855 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1366 = (4683:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1366
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1367) ≤ val WuPaper.ClassicalFourthData.Bq 1367
    have hp : val WuPaper.ClassicalFourthData.Bq 1367 = (125536343364920:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1367 = 125536343364920 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1367 = (9367:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1367
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1368) ≤ val WuPaper.ClassicalFourthData.Bq 1368
    have hp : val WuPaper.ClassicalFourthData.Bq 1368 = (125602492975872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1368 = 125602492975872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1368 = (1171:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1368
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1369) ≤ val WuPaper.ClassicalFourthData.Bq 1369
    have hp : val WuPaper.ClassicalFourthData.Bq 1369 = (125668613649501:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1369 = 125668613649501 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1369 = (9369:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1369
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1370) ≤ val WuPaper.ClassicalFourthData.Bq 1370
    have hp : val WuPaper.ClassicalFourthData.Bq 1370 = (125734705400591:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1370 = 125734705400591 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1370 = (937:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1370
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1371) ≤ val WuPaper.ClassicalFourthData.Bq 1371
    have hp : val WuPaper.ClassicalFourthData.Bq 1371 = (125800768243915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1371 = 125800768243915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1371 = (9371:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1371
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1372) ≤ val WuPaper.ClassicalFourthData.Bq 1372
    have hp : val WuPaper.ClassicalFourthData.Bq 1372 = (125866802194239:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1372 = 125866802194239 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1372 = (2343:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1372
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1373) ≤ val WuPaper.ClassicalFourthData.Bq 1373
    have hp : val WuPaper.ClassicalFourthData.Bq 1373 = (125932807266316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1373 = 125932807266316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1373 = (9373:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1373
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1374) ≤ val WuPaper.ClassicalFourthData.Bq 1374
    have hp : val WuPaper.ClassicalFourthData.Bq 1374 = (125998783474892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1374 = 125998783474892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1374 = (4687:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1374
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1375) ≤ val WuPaper.ClassicalFourthData.Bq 1375
    have hp : val WuPaper.ClassicalFourthData.Bq 1375 = (126064730834704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1375 = 126064730834704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1375 = (75:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1375
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_085
