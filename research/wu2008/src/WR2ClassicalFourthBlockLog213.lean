import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints213
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_213 (j : Fin 16) (hj : 16*213+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*213+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*213+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3408) ≤ val WuPaper.ClassicalFourthData.Bq 3408
    have hp : val WuPaper.ClassicalFourthData.Bq 3408 = (216082095450207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3408 = 216082095450207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3408 = (713:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3408
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3409) ≤ val WuPaper.ClassicalFourthData.Bq 3409
    have hp : val WuPaper.ClassicalFourthData.Bq 3409 = (216110479906961:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3409 = 216110479906961 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3409 = (11409:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3409
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3410) ≤ val WuPaper.ClassicalFourthData.Bq 3410
    have hp : val WuPaper.ClassicalFourthData.Bq 3410 = (216138853001965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3410 = 216138853001965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3410 = (1141:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3410
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3411) ≤ val WuPaper.ClassicalFourthData.Bq 3411
    have hp : val WuPaper.ClassicalFourthData.Bq 3411 = (216167214739929:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3411 = 216167214739929 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3411 = (11411:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3411
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3412) ≤ val WuPaper.ClassicalFourthData.Bq 3412
    have hp : val WuPaper.ClassicalFourthData.Bq 3412 = (216195565125561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3412 = 216195565125561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3412 = (2853:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3412
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3413) ≤ val WuPaper.ClassicalFourthData.Bq 3413
    have hp : val WuPaper.ClassicalFourthData.Bq 3413 = (216223904163566:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3413 = 216223904163566 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3413 = (11413:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3413
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3414) ≤ val WuPaper.ClassicalFourthData.Bq 3414
    have hp : val WuPaper.ClassicalFourthData.Bq 3414 = (216252231858648:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3414 = 216252231858648 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3414 = (5707:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3414
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3415) ≤ val WuPaper.ClassicalFourthData.Bq 3415
    have hp : val WuPaper.ClassicalFourthData.Bq 3415 = (216280548215508:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3415 = 216280548215508 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3415 = (2283:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3415
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3416) ≤ val WuPaper.ClassicalFourthData.Bq 3416
    have hp : val WuPaper.ClassicalFourthData.Bq 3416 = (216308853238845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3416 = 216308853238845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3416 = (1427:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3416
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3417) ≤ val WuPaper.ClassicalFourthData.Bq 3417
    have hp : val WuPaper.ClassicalFourthData.Bq 3417 = (216337146933356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3417 = 216337146933356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3417 = (11417:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3417
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3418) ≤ val WuPaper.ClassicalFourthData.Bq 3418
    have hp : val WuPaper.ClassicalFourthData.Bq 3418 = (216365429303734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3418 = 216365429303734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3418 = (5709:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3418
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3419) ≤ val WuPaper.ClassicalFourthData.Bq 3419
    have hp : val WuPaper.ClassicalFourthData.Bq 3419 = (216393700354672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3419 = 216393700354672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3419 = (11419:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3419
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3420) ≤ val WuPaper.ClassicalFourthData.Bq 3420
    have hp : val WuPaper.ClassicalFourthData.Bq 3420 = (216421960090858:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3420 = 216421960090858 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3420 = (571:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3420
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3421) ≤ val WuPaper.ClassicalFourthData.Bq 3421
    have hp : val WuPaper.ClassicalFourthData.Bq 3421 = (216450208516980:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3421 = 216450208516980 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3421 = (11421:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3421
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3422) ≤ val WuPaper.ClassicalFourthData.Bq 3422
    have hp : val WuPaper.ClassicalFourthData.Bq 3422 = (216478445637723:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3422 = 216478445637723 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3422 = (5711:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3422
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3423) ≤ val WuPaper.ClassicalFourthData.Bq 3423
    have hp : val WuPaper.ClassicalFourthData.Bq 3423 = (216506671457768:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3423 = 216506671457768 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3423 = (11423:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3423
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_213
