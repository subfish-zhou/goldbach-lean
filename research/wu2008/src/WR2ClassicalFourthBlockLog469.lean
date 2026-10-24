import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints469
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_469 (j : Fin 16) (hj : 16*469+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*469+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*469+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7504) ≤ val WuPaper.ClassicalFourthData.Bq 7504
    have hp : val WuPaper.ClassicalFourthData.Bq 7504 = (272549133090728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7504 = 272549133090728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7504 = (969:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7504
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7505) ≤ val WuPaper.ClassicalFourthData.Bq 7505
    have hp : val WuPaper.ClassicalFourthData.Bq 7505 = (272553979327521:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7505 = 272553979327521 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7505 = (3101:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7505
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7506) ≤ val WuPaper.ClassicalFourthData.Bq 7506
    have hp : val WuPaper.ClassicalFourthData.Bq 7506 = (272558822990346:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7506 = 272558822990346 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7506 = (7753:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7506
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7507) ≤ val WuPaper.ClassicalFourthData.Bq 7507
    have hp : val WuPaper.ClassicalFourthData.Bq 7507 = (272563664080041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7507 = 272563664080041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7507 = (15507:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7507
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7508) ≤ val WuPaper.ClassicalFourthData.Bq 7508
    have hp : val WuPaper.ClassicalFourthData.Bq 7508 = (272568502597441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7508 = 272568502597441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7508 = (3877:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7508
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7509) ≤ val WuPaper.ClassicalFourthData.Bq 7509
    have hp : val WuPaper.ClassicalFourthData.Bq 7509 = (272573338543384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7509 = 272573338543384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7509 = (15509:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7509
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7510) ≤ val WuPaper.ClassicalFourthData.Bq 7510
    have hp : val WuPaper.ClassicalFourthData.Bq 7510 = (272578171918704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7510 = 272578171918704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7510 = (1551:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7510
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7511) ≤ val WuPaper.ClassicalFourthData.Bq 7511
    have hp : val WuPaper.ClassicalFourthData.Bq 7511 = (272583002724237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7511 = 272583002724237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7511 = (15511:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7511
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7512) ≤ val WuPaper.ClassicalFourthData.Bq 7512
    have hp : val WuPaper.ClassicalFourthData.Bq 7512 = (272587830960818:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7512 = 272587830960818 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7512 = (1939:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7512
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7513) ≤ val WuPaper.ClassicalFourthData.Bq 7513
    have hp : val WuPaper.ClassicalFourthData.Bq 7513 = (272592656629283:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7513 = 272592656629283 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7513 = (15513:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7513
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7514) ≤ val WuPaper.ClassicalFourthData.Bq 7514
    have hp : val WuPaper.ClassicalFourthData.Bq 7514 = (272597479730465:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7514 = 272597479730465 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7514 = (7757:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7514
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7515) ≤ val WuPaper.ClassicalFourthData.Bq 7515
    have hp : val WuPaper.ClassicalFourthData.Bq 7515 = (272602300265199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7515 = 272602300265199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7515 = (3103:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7515
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7516) ≤ val WuPaper.ClassicalFourthData.Bq 7516
    have hp : val WuPaper.ClassicalFourthData.Bq 7516 = (272607118234319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7516 = 272607118234319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7516 = (3879:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7516
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7517) ≤ val WuPaper.ClassicalFourthData.Bq 7517
    have hp : val WuPaper.ClassicalFourthData.Bq 7517 = (272611933638659:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7517 = 272611933638659 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7517 = (15517:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7517
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7518) ≤ val WuPaper.ClassicalFourthData.Bq 7518
    have hp : val WuPaper.ClassicalFourthData.Bq 7518 = (272616746479051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7518 = 272616746479051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7518 = (7759:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7518
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7519) ≤ val WuPaper.ClassicalFourthData.Bq 7519
    have hp : val WuPaper.ClassicalFourthData.Bq 7519 = (272621556756330:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7519 = 272621556756330 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7519 = (15519:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7519
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_469
