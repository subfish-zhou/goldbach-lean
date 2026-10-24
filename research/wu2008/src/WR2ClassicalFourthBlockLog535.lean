import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints535
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_535 (j : Fin 16) (hj : 16*535+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*535+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*535+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8560) ≤ val WuPaper.ClassicalFourthData.Bq 8560
    have hp : val WuPaper.ClassicalFourthData.Bq 8560 = (276382318823196:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8560 = 276382318823196 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8560 = (207:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8560
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8561) ≤ val WuPaper.ClassicalFourthData.Bq 8561
    have hp : val WuPaper.ClassicalFourthData.Bq 8561 = (276384859511650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8561 = 276384859511650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8561 = (16561:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8561
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8562) ≤ val WuPaper.ClassicalFourthData.Bq 8562
    have hp : val WuPaper.ClassicalFourthData.Bq 8562 = (276387398362565:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8562 = 276387398362565 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8562 = (8281:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8562
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8563) ≤ val WuPaper.ClassicalFourthData.Bq 8563
    have hp : val WuPaper.ClassicalFourthData.Bq 8563 = (276389935376515:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8563 = 276389935376515 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8563 = (16563:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8563
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8564) ≤ val WuPaper.ClassicalFourthData.Bq 8564
    have hp : val WuPaper.ClassicalFourthData.Bq 8564 = (276392470554079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8564 = 276392470554079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8564 = (4141:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8564
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8565) ≤ val WuPaper.ClassicalFourthData.Bq 8565
    have hp : val WuPaper.ClassicalFourthData.Bq 8565 = (276395003895831:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8565 = 276395003895831 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8565 = (3313:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8565
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8566) ≤ val WuPaper.ClassicalFourthData.Bq 8566
    have hp : val WuPaper.ClassicalFourthData.Bq 8566 = (276397535402348:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8566 = 276397535402348 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8566 = (8283:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8566
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8567) ≤ val WuPaper.ClassicalFourthData.Bq 8567
    have hp : val WuPaper.ClassicalFourthData.Bq 8567 = (276400065074206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8567 = 276400065074206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8567 = (16567:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8567
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8568) ≤ val WuPaper.ClassicalFourthData.Bq 8568
    have hp : val WuPaper.ClassicalFourthData.Bq 8568 = (276402592911980:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8568 = 276402592911980 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8568 = (2071:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8568
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8569) ≤ val WuPaper.ClassicalFourthData.Bq 8569
    have hp : val WuPaper.ClassicalFourthData.Bq 8569 = (276405118916245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8569 = 276405118916245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8569 = (16569:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8569
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8570) ≤ val WuPaper.ClassicalFourthData.Bq 8570
    have hp : val WuPaper.ClassicalFourthData.Bq 8570 = (276407643087577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8570 = 276407643087577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8570 = (1657:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8570
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8571) ≤ val WuPaper.ClassicalFourthData.Bq 8571
    have hp : val WuPaper.ClassicalFourthData.Bq 8571 = (276410165426550:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8571 = 276410165426550 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8571 = (16571:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8571
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8572) ≤ val WuPaper.ClassicalFourthData.Bq 8572
    have hp : val WuPaper.ClassicalFourthData.Bq 8572 = (276412685933740:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8572 = 276412685933740 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8572 = (4143:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8572
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8573) ≤ val WuPaper.ClassicalFourthData.Bq 8573
    have hp : val WuPaper.ClassicalFourthData.Bq 8573 = (276415204609720:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8573 = 276415204609720 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8573 = (16573:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8573
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8574) ≤ val WuPaper.ClassicalFourthData.Bq 8574
    have hp : val WuPaper.ClassicalFourthData.Bq 8574 = (276417721455065:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8574 = 276417721455065 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8574 = (8287:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8574
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8575) ≤ val WuPaper.ClassicalFourthData.Bq 8575
    have hp : val WuPaper.ClassicalFourthData.Bq 8575 = (276420236470350:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8575 = 276420236470350 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8575 = (663:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_535
