import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints275
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_275 (j : Fin 16) (hj : 16*275+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*275+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*275+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4400) ≤ val WuPaper.ClassicalFourthData.Bq 4400
    have hp : val WuPaper.ClassicalFourthData.Bq 4400 = (239334627332058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4400 = 239334627332058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4400 = (31:ℝ)/10 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4400
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4401) ≤ val WuPaper.ClassicalFourthData.Bq 4401
    have hp : val WuPaper.ClassicalFourthData.Bq 4401 = (239353724784395:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4401 = 239353724784395 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4401 = (12401:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4401
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4402) ≤ val WuPaper.ClassicalFourthData.Bq 4402
    have hp : val WuPaper.ClassicalFourthData.Bq 4402 = (239372814587099:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4402 = 239372814587099 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4402 = (6201:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4402
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4403) ≤ val WuPaper.ClassicalFourthData.Bq 4403
    have hp : val WuPaper.ClassicalFourthData.Bq 4403 = (239391896743108:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4403 = 239391896743108 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4403 = (12403:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4403
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4404) ≤ val WuPaper.ClassicalFourthData.Bq 4404
    have hp : val WuPaper.ClassicalFourthData.Bq 4404 = (239410971255358:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4404 = 239410971255358 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4404 = (3101:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4404
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4405) ≤ val WuPaper.ClassicalFourthData.Bq 4405
    have hp : val WuPaper.ClassicalFourthData.Bq 4405 = (239430038126784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4405 = 239430038126784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4405 = (2481:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4405
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4406) ≤ val WuPaper.ClassicalFourthData.Bq 4406
    have hp : val WuPaper.ClassicalFourthData.Bq 4406 = (239449097360321:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4406 = 239449097360321 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4406 = (6203:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4406
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4407) ≤ val WuPaper.ClassicalFourthData.Bq 4407
    have hp : val WuPaper.ClassicalFourthData.Bq 4407 = (239468148958901:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4407 = 239468148958901 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4407 = (12407:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4407
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4408) ≤ val WuPaper.ClassicalFourthData.Bq 4408
    have hp : val WuPaper.ClassicalFourthData.Bq 4408 = (239487192925455:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4408 = 239487192925455 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4408 = (1551:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4408
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4409) ≤ val WuPaper.ClassicalFourthData.Bq 4409
    have hp : val WuPaper.ClassicalFourthData.Bq 4409 = (239506229262913:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4409 = 239506229262913 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4409 = (12409:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4409
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4410) ≤ val WuPaper.ClassicalFourthData.Bq 4410
    have hp : val WuPaper.ClassicalFourthData.Bq 4410 = (239525257974204:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4410 = 239525257974204 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4410 = (1241:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4410
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4411) ≤ val WuPaper.ClassicalFourthData.Bq 4411
    have hp : val WuPaper.ClassicalFourthData.Bq 4411 = (239544279062255:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4411 = 239544279062255 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4411 = (12411:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4411
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4412) ≤ val WuPaper.ClassicalFourthData.Bq 4412
    have hp : val WuPaper.ClassicalFourthData.Bq 4412 = (239563292529992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4412 = 239563292529992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4412 = (3103:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4412
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4413) ≤ val WuPaper.ClassicalFourthData.Bq 4413
    have hp : val WuPaper.ClassicalFourthData.Bq 4413 = (239582298380339:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4413 = 239582298380339 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4413 = (12413:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4413
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4414) ≤ val WuPaper.ClassicalFourthData.Bq 4414
    have hp : val WuPaper.ClassicalFourthData.Bq 4414 = (239601296616220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4414 = 239601296616220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4414 = (6207:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4414
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4415) ≤ val WuPaper.ClassicalFourthData.Bq 4415
    have hp : val WuPaper.ClassicalFourthData.Bq 4415 = (239620287240557:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4415 = 239620287240557 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4415 = (2483:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4415
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_275
