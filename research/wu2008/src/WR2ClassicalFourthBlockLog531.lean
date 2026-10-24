import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints531
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_531 (j : Fin 16) (hj : 16*531+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*531+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*531+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8496) ≤ val WuPaper.ClassicalFourthData.Bq 8496
    have hp : val WuPaper.ClassicalFourthData.Bq 8496 = (276215866145585:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8496 = 276215866145585 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8496 = (1031:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8496
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8497) ≤ val WuPaper.ClassicalFourthData.Bq 8497
    have hp : val WuPaper.ClassicalFourthData.Bq 8497 = (276218525644838:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8497 = 276218525644838 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8497 = (16497:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8497
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8498) ≤ val WuPaper.ClassicalFourthData.Bq 8498
    have hp : val WuPaper.ClassicalFourthData.Bq 8498 = (276221183269240:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8498 = 276221183269240 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8498 = (8249:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8498
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8499) ≤ val WuPaper.ClassicalFourthData.Bq 8499
    have hp : val WuPaper.ClassicalFourthData.Bq 8499 = (276223839019380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8499 = 276223839019380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8499 = (16499:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8499
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8500) ≤ val WuPaper.ClassicalFourthData.Bq 8500
    have hp : val WuPaper.ClassicalFourthData.Bq 8500 = (276226492895848:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8500 = 276226492895848 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8500 = (33:ℝ)/8 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8500
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8501) ≤ val WuPaper.ClassicalFourthData.Bq 8501
    have hp : val WuPaper.ClassicalFourthData.Bq 8501 = (276229144899232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8501 = 276229144899232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8501 = (16501:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8501
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8502) ≤ val WuPaper.ClassicalFourthData.Bq 8502
    have hp : val WuPaper.ClassicalFourthData.Bq 8502 = (276231795030121:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8502 = 276231795030121 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8502 = (8251:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8502
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8503) ≤ val WuPaper.ClassicalFourthData.Bq 8503
    have hp : val WuPaper.ClassicalFourthData.Bq 8503 = (276234443289104:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8503 = 276234443289104 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8503 = (16503:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8503
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8504) ≤ val WuPaper.ClassicalFourthData.Bq 8504
    have hp : val WuPaper.ClassicalFourthData.Bq 8504 = (276237089676769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8504 = 276237089676769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8504 = (2063:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8504
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8505) ≤ val WuPaper.ClassicalFourthData.Bq 8505
    have hp : val WuPaper.ClassicalFourthData.Bq 8505 = (276239734193703:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8505 = 276239734193703 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8505 = (3301:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8505
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8506) ≤ val WuPaper.ClassicalFourthData.Bq 8506
    have hp : val WuPaper.ClassicalFourthData.Bq 8506 = (276242376840496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8506 = 276242376840496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8506 = (8253:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8506
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8507) ≤ val WuPaper.ClassicalFourthData.Bq 8507
    have hp : val WuPaper.ClassicalFourthData.Bq 8507 = (276245017617734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8507 = 276245017617734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8507 = (16507:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8507
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8508) ≤ val WuPaper.ClassicalFourthData.Bq 8508
    have hp : val WuPaper.ClassicalFourthData.Bq 8508 = (276247656526005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8508 = 276247656526005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8508 = (4127:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8508
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8509) ≤ val WuPaper.ClassicalFourthData.Bq 8509
    have hp : val WuPaper.ClassicalFourthData.Bq 8509 = (276250293565896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8509 = 276250293565896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8509 = (16509:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8509
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8510) ≤ val WuPaper.ClassicalFourthData.Bq 8510
    have hp : val WuPaper.ClassicalFourthData.Bq 8510 = (276252928737995:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8510 = 276252928737995 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8510 = (1651:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8510
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8511) ≤ val WuPaper.ClassicalFourthData.Bq 8511
    have hp : val WuPaper.ClassicalFourthData.Bq 8511 = (276255562042888:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8511 = 276255562042888 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8511 = (16511:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_531
