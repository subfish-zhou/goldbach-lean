import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints217
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_217 (j : Fin 16) (hj : 16*217+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*217+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*217+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3472) ≤ val WuPaper.ClassicalFourthData.Bq 3472
    have hp : val WuPaper.ClassicalFourthData.Bq 3472 = (217875990169684:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3472 = 217875990169684 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3472 = (717:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3472
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3473) ≤ val WuPaper.ClassicalFourthData.Bq 3473
    have hp : val WuPaper.ClassicalFourthData.Bq 3473 = (217903656873795:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3473 = 217903656873795 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3473 = (11473:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3473
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3474) ≤ val WuPaper.ClassicalFourthData.Bq 3474
    have hp : val WuPaper.ClassicalFourthData.Bq 3474 = (217931312512952:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3474 = 217931312512952 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3474 = (5737:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3474
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3475) ≤ val WuPaper.ClassicalFourthData.Bq 3475
    have hp : val WuPaper.ClassicalFourthData.Bq 3475 = (217958957091716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3475 = 217958957091716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3475 = (459:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3475
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3476) ≤ val WuPaper.ClassicalFourthData.Bq 3476
    have hp : val WuPaper.ClassicalFourthData.Bq 3476 = (217986590614649:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3476 = 217986590614649 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3476 = (2869:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3476
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3477) ≤ val WuPaper.ClassicalFourthData.Bq 3477
    have hp : val WuPaper.ClassicalFourthData.Bq 3477 = (218014213086308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3477 = 218014213086308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3477 = (11477:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3477
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3478) ≤ val WuPaper.ClassicalFourthData.Bq 3478
    have hp : val WuPaper.ClassicalFourthData.Bq 3478 = (218041824511250:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3478 = 218041824511250 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3478 = (5739:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3478
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3479) ≤ val WuPaper.ClassicalFourthData.Bq 3479
    have hp : val WuPaper.ClassicalFourthData.Bq 3479 = (218069424894030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3479 = 218069424894030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3479 = (11479:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3479
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3480) ≤ val WuPaper.ClassicalFourthData.Bq 3480
    have hp : val WuPaper.ClassicalFourthData.Bq 3480 = (218097014239197:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3480 = 218097014239197 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3480 = (287:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3480
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3481) ≤ val WuPaper.ClassicalFourthData.Bq 3481
    have hp : val WuPaper.ClassicalFourthData.Bq 3481 = (218124592551303:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3481 = 218124592551303 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3481 = (11481:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3481
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3482) ≤ val WuPaper.ClassicalFourthData.Bq 3482
    have hp : val WuPaper.ClassicalFourthData.Bq 3482 = (218152159834895:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3482 = 218152159834895 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3482 = (5741:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3482
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3483) ≤ val WuPaper.ClassicalFourthData.Bq 3483
    have hp : val WuPaper.ClassicalFourthData.Bq 3483 = (218179716094516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3483 = 218179716094516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3483 = (11483:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3483
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3484) ≤ val WuPaper.ClassicalFourthData.Bq 3484
    have hp : val WuPaper.ClassicalFourthData.Bq 3484 = (218207261334711:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3484 = 218207261334711 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3484 = (2871:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3484
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3485) ≤ val WuPaper.ClassicalFourthData.Bq 3485
    have hp : val WuPaper.ClassicalFourthData.Bq 3485 = (218234795560018:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3485 = 218234795560018 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3485 = (2297:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3485
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3486) ≤ val WuPaper.ClassicalFourthData.Bq 3486
    have hp : val WuPaper.ClassicalFourthData.Bq 3486 = (218262318774978:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3486 = 218262318774978 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3486 = (5743:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3486
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3487) ≤ val WuPaper.ClassicalFourthData.Bq 3487
    have hp : val WuPaper.ClassicalFourthData.Bq 3487 = (218289830984124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3487 = 218289830984124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3487 = (11487:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3487
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_217
