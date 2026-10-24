import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints215
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_215 (j : Fin 16) (hj : 16*215+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*215+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*215+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3440) ≤ val WuPaper.ClassicalFourthData.Bq 3440
    have hp : val WuPaper.ClassicalFourthData.Bq 3440 = (216984785917871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3440 = 216984785917871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3440 = (143:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3440
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3441) ≤ val WuPaper.ClassicalFourthData.Bq 3441
    have hp : val WuPaper.ClassicalFourthData.Bq 3441 = (217012809123411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3441 = 217012809123411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3441 = (11441:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3441
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3442) ≤ val WuPaper.ClassicalFourthData.Bq 3442
    have hp : val WuPaper.ClassicalFourthData.Bq 3442 = (217040821116777:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3442 = 217040821116777 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3442 = (5721:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3442
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3443) ≤ val WuPaper.ClassicalFourthData.Bq 3443
    have hp : val WuPaper.ClassicalFourthData.Bq 3443 = (217068821902608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3443 = 217068821902608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3443 = (11443:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3443
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3444) ≤ val WuPaper.ClassicalFourthData.Bq 3444
    have hp : val WuPaper.ClassicalFourthData.Bq 3444 = (217096811485535:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3444 = 217096811485535 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3444 = (2861:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3444
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3445) ≤ val WuPaper.ClassicalFourthData.Bq 3445
    have hp : val WuPaper.ClassicalFourthData.Bq 3445 = (217124789870191:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3445 = 217124789870191 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3445 = (2289:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3445
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3446) ≤ val WuPaper.ClassicalFourthData.Bq 3446
    have hp : val WuPaper.ClassicalFourthData.Bq 3446 = (217152757061204:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3446 = 217152757061204 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3446 = (5723:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3446
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3447) ≤ val WuPaper.ClassicalFourthData.Bq 3447
    have hp : val WuPaper.ClassicalFourthData.Bq 3447 = (217180713063202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3447 = 217180713063202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3447 = (11447:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3447
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3448) ≤ val WuPaper.ClassicalFourthData.Bq 3448
    have hp : val WuPaper.ClassicalFourthData.Bq 3448 = (217208657880809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3448 = 217208657880809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3448 = (1431:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3448
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3449) ≤ val WuPaper.ClassicalFourthData.Bq 3449
    have hp : val WuPaper.ClassicalFourthData.Bq 3449 = (217236591518648:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3449 = 217236591518648 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3449 = (11449:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3449
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3450) ≤ val WuPaper.ClassicalFourthData.Bq 3450
    have hp : val WuPaper.ClassicalFourthData.Bq 3450 = (217264513981338:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3450 = 217264513981338 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3450 = (229:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3450
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3451) ≤ val WuPaper.ClassicalFourthData.Bq 3451
    have hp : val WuPaper.ClassicalFourthData.Bq 3451 = (217292425273496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3451 = 217292425273496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3451 = (11451:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3451
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3452) ≤ val WuPaper.ClassicalFourthData.Bq 3452
    have hp : val WuPaper.ClassicalFourthData.Bq 3452 = (217320325399739:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3452 = 217320325399739 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3452 = (2863:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3452
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3453) ≤ val WuPaper.ClassicalFourthData.Bq 3453
    have hp : val WuPaper.ClassicalFourthData.Bq 3453 = (217348214364679:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3453 = 217348214364679 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3453 = (11453:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3453
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3454) ≤ val WuPaper.ClassicalFourthData.Bq 3454
    have hp : val WuPaper.ClassicalFourthData.Bq 3454 = (217376092172927:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3454 = 217376092172927 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3454 = (5727:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3454
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3455) ≤ val WuPaper.ClassicalFourthData.Bq 3455
    have hp : val WuPaper.ClassicalFourthData.Bq 3455 = (217403958829092:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3455 = 217403958829092 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3455 = (2291:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3455
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_215
