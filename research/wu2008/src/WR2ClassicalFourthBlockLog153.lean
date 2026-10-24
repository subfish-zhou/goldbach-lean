import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints153
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_153 (j : Fin 16) (hj : 16*153+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*153+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*153+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2448) ≤ val WuPaper.ClassicalFourthData.Bq 2448
    have hp : val WuPaper.ClassicalFourthData.Bq 2448 = (182800782574440:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2448 = 182800782574440 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2448 = (653:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2448
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2449) ≤ val WuPaper.ClassicalFourthData.Bq 2449
    have hp : val WuPaper.ClassicalFourthData.Bq 2449 = (182842652467548:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2449 = 182842652467548 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2449 = (10449:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2449
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2450) ≤ val WuPaper.ClassicalFourthData.Bq 2450
    have hp : val WuPaper.ClassicalFourthData.Bq 2450 = (182884505143652:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2450 = 182884505143652 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2450 = (209:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2450
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2451) ≤ val WuPaper.ClassicalFourthData.Bq 2451
    have hp : val WuPaper.ClassicalFourthData.Bq 2451 = (182926340610550:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2451 = 182926340610550 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2451 = (10451:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2451
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2452) ≤ val WuPaper.ClassicalFourthData.Bq 2452
    have hp : val WuPaper.ClassicalFourthData.Bq 2452 = (182968158876033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2452 = 182968158876033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2452 = (2613:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2452
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2453) ≤ val WuPaper.ClassicalFourthData.Bq 2453
    have hp : val WuPaper.ClassicalFourthData.Bq 2453 = (183009959947886:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2453 = 183009959947886 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2453 = (10453:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2453
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2454) ≤ val WuPaper.ClassicalFourthData.Bq 2454
    have hp : val WuPaper.ClassicalFourthData.Bq 2454 = (183051743833894:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2454 = 183051743833894 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2454 = (5227:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2454
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2455) ≤ val WuPaper.ClassicalFourthData.Bq 2455
    have hp : val WuPaper.ClassicalFourthData.Bq 2455 = (183093510541833:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2455 = 183093510541833 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2455 = (2091:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2455
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2456) ≤ val WuPaper.ClassicalFourthData.Bq 2456
    have hp : val WuPaper.ClassicalFourthData.Bq 2456 = (183135260079479:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2456 = 183135260079479 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2456 = (1307:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2456
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2457) ≤ val WuPaper.ClassicalFourthData.Bq 2457
    have hp : val WuPaper.ClassicalFourthData.Bq 2457 = (183176992454601:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2457 = 183176992454601 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2457 = (10457:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2457
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2458) ≤ val WuPaper.ClassicalFourthData.Bq 2458
    have hp : val WuPaper.ClassicalFourthData.Bq 2458 = (183218707674964:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2458 = 183218707674964 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2458 = (5229:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2458
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2459) ≤ val WuPaper.ClassicalFourthData.Bq 2459
    have hp : val WuPaper.ClassicalFourthData.Bq 2459 = (183260405748330:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2459 = 183260405748330 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2459 = (10459:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2459
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2460) ≤ val WuPaper.ClassicalFourthData.Bq 2460
    have hp : val WuPaper.ClassicalFourthData.Bq 2460 = (183302086682456:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2460 = 183302086682456 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2460 = (523:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2460
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2461) ≤ val WuPaper.ClassicalFourthData.Bq 2461
    have hp : val WuPaper.ClassicalFourthData.Bq 2461 = (183343750485093:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2461 = 183343750485093 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2461 = (10461:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2461
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2462) ≤ val WuPaper.ClassicalFourthData.Bq 2462
    have hp : val WuPaper.ClassicalFourthData.Bq 2462 = (183385397163991:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2462 = 183385397163991 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2462 = (5231:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2462
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2463) ≤ val WuPaper.ClassicalFourthData.Bq 2463
    have hp : val WuPaper.ClassicalFourthData.Bq 2463 = (183427026726893:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2463 = 183427026726893 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2463 = (10463:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2463
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_153
