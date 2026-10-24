import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints152
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_152 (j : Fin 16) (hj : 16*152+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*152+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*152+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2432) ≤ val WuPaper.ClassicalFourthData.Bq 2432
    have hp : val WuPaper.ClassicalFourthData.Bq 2432 = (182128516394469:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2432 = 182128516394469 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2432 = (326:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2432
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2433) ≤ val WuPaper.ClassicalFourthData.Bq 2433
    have hp : val WuPaper.ClassicalFourthData.Bq 2433 = (182170662823339:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2433 = 182170662823339 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2433 = (10433:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2433
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2434) ≤ val WuPaper.ClassicalFourthData.Bq 2434
    have hp : val WuPaper.ClassicalFourthData.Bq 2434 = (182212791909889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2434 = 182212791909889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2434 = (5217:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2434
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2435) ≤ val WuPaper.ClassicalFourthData.Bq 2435
    have hp : val WuPaper.ClassicalFourthData.Bq 2435 = (182254903661984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2435 = 182254903661984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2435 = (2087:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2435
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2436) ≤ val WuPaper.ClassicalFourthData.Bq 2436
    have hp : val WuPaper.ClassicalFourthData.Bq 2436 = (182296998087485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2436 = 182296998087485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2436 = (2609:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2436
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2437) ≤ val WuPaper.ClassicalFourthData.Bq 2437
    have hp : val WuPaper.ClassicalFourthData.Bq 2437 = (182339075194247:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2437 = 182339075194247 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2437 = (10437:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2437
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2438) ≤ val WuPaper.ClassicalFourthData.Bq 2438
    have hp : val WuPaper.ClassicalFourthData.Bq 2438 = (182381134990123:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2438 = 182381134990123 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2438 = (5219:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2438
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2439) ≤ val WuPaper.ClassicalFourthData.Bq 2439
    have hp : val WuPaper.ClassicalFourthData.Bq 2439 = (182423177482961:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2439 = 182423177482961 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2439 = (10439:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2439
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2440) ≤ val WuPaper.ClassicalFourthData.Bq 2440
    have hp : val WuPaper.ClassicalFourthData.Bq 2440 = (182465202680603:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2440 = 182465202680603 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2440 = (261:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2440
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2441) ≤ val WuPaper.ClassicalFourthData.Bq 2441
    have hp : val WuPaper.ClassicalFourthData.Bq 2441 = (182507210590888:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2441 = 182507210590888 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2441 = (10441:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2441
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2442) ≤ val WuPaper.ClassicalFourthData.Bq 2442
    have hp : val WuPaper.ClassicalFourthData.Bq 2442 = (182549201221650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2442 = 182549201221650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2442 = (5221:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2442
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2443) ≤ val WuPaper.ClassicalFourthData.Bq 2443
    have hp : val WuPaper.ClassicalFourthData.Bq 2443 = (182591174580721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2443 = 182591174580721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2443 = (10443:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2443
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2444) ≤ val WuPaper.ClassicalFourthData.Bq 2444
    have hp : val WuPaper.ClassicalFourthData.Bq 2444 = (182633130675924:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2444 = 182633130675924 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2444 = (2611:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2444
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2445) ≤ val WuPaper.ClassicalFourthData.Bq 2445
    have hp : val WuPaper.ClassicalFourthData.Bq 2445 = (182675069515083:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2445 = 182675069515083 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2445 = (2089:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2445
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2446) ≤ val WuPaper.ClassicalFourthData.Bq 2446
    have hp : val WuPaper.ClassicalFourthData.Bq 2446 = (182716991106014:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2446 = 182716991106014 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2446 = (5223:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2446
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2447) ≤ val WuPaper.ClassicalFourthData.Bq 2447
    have hp : val WuPaper.ClassicalFourthData.Bq 2447 = (182758895456531:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2447 = 182758895456531 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2447 = (10447:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_152
