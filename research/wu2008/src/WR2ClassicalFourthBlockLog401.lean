import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints401
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_401 (j : Fin 16) (hj : 16*401+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*401+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*401+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6416) ≤ val WuPaper.ClassicalFourthData.Bq 6416
    have hp : val WuPaper.ClassicalFourthData.Bq 6416 = (265551810306986:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6416 = 265551810306986 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6416 = (901:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6416
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6417) ≤ val WuPaper.ClassicalFourthData.Bq 6417
    have hp : val WuPaper.ClassicalFourthData.Bq 6417 = (265560026602616:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6417 = 265560026602616 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6417 = (14417:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6417
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6418) ≤ val WuPaper.ClassicalFourthData.Bq 6418
    have hp : val WuPaper.ClassicalFourthData.Bq 6418 = (265568239201877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6418 = 265568239201877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6418 = (7209:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6418
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6419) ≤ val WuPaper.ClassicalFourthData.Bq 6419
    have hp : val WuPaper.ClassicalFourthData.Bq 6419 = (265576448106030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6419 = 265576448106030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6419 = (14419:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6419
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6420) ≤ val WuPaper.ClassicalFourthData.Bq 6420
    have hp : val WuPaper.ClassicalFourthData.Bq 6420 = (265584653316335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6420 = 265584653316335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6420 = (721:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6420
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6421) ≤ val WuPaper.ClassicalFourthData.Bq 6421
    have hp : val WuPaper.ClassicalFourthData.Bq 6421 = (265592854834050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6421 = 265592854834050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6421 = (14421:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6421
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6422) ≤ val WuPaper.ClassicalFourthData.Bq 6422
    have hp : val WuPaper.ClassicalFourthData.Bq 6422 = (265601052660433:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6422 = 265601052660433 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6422 = (7211:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6422
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6423) ≤ val WuPaper.ClassicalFourthData.Bq 6423
    have hp : val WuPaper.ClassicalFourthData.Bq 6423 = (265609246796742:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6423 = 265609246796742 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6423 = (14423:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6423
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6424) ≤ val WuPaper.ClassicalFourthData.Bq 6424
    have hp : val WuPaper.ClassicalFourthData.Bq 6424 = (265617437244235:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6424 = 265617437244235 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6424 = (1803:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6424
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6425) ≤ val WuPaper.ClassicalFourthData.Bq 6425
    have hp : val WuPaper.ClassicalFourthData.Bq 6425 = (265625624004168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6425 = 265625624004168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6425 = (577:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6425
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6426) ≤ val WuPaper.ClassicalFourthData.Bq 6426
    have hp : val WuPaper.ClassicalFourthData.Bq 6426 = (265633807077799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6426 = 265633807077799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6426 = (7213:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6426
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6427) ≤ val WuPaper.ClassicalFourthData.Bq 6427
    have hp : val WuPaper.ClassicalFourthData.Bq 6427 = (265641986466382:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6427 = 265641986466382 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6427 = (14427:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6427
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6428) ≤ val WuPaper.ClassicalFourthData.Bq 6428
    have hp : val WuPaper.ClassicalFourthData.Bq 6428 = (265650162171174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6428 = 265650162171174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6428 = (3607:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6428
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6429) ≤ val WuPaper.ClassicalFourthData.Bq 6429
    have hp : val WuPaper.ClassicalFourthData.Bq 6429 = (265658334193428:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6429 = 265658334193428 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6429 = (14429:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6429
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6430) ≤ val WuPaper.ClassicalFourthData.Bq 6430
    have hp : val WuPaper.ClassicalFourthData.Bq 6430 = (265666502534400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6430 = 265666502534400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6430 = (1443:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6430
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6431) ≤ val WuPaper.ClassicalFourthData.Bq 6431
    have hp : val WuPaper.ClassicalFourthData.Bq 6431 = (265674667195344:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6431 = 265674667195344 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6431 = (14431:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6431
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_401
