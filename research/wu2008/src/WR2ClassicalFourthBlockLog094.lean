import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints094
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_094 (j : Fin 16) (hj : 16*94+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*94+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*94+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1504) ≤ val WuPaper.ClassicalFourthData.Bq 1504
    have hp : val WuPaper.ClassicalFourthData.Bq 1504 = (134335328077085:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1504 = 134335328077085 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1504 = (297:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1504
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1505) ≤ val WuPaper.ClassicalFourthData.Bq 1505
    have hp : val WuPaper.ClassicalFourthData.Bq 1505 = (134397647156130:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1505 = 134397647156130 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1505 = (1901:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1505
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1506) ≤ val WuPaper.ClassicalFourthData.Bq 1506
    have hp : val WuPaper.ClassicalFourthData.Bq 1506 = (134459939238597:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1506 = 134459939238597 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1506 = (4753:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1506
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1507) ≤ val WuPaper.ClassicalFourthData.Bq 1507
    have hp : val WuPaper.ClassicalFourthData.Bq 1507 = (134522204338048:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1507 = 134522204338048 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1507 = (9507:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1507
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1508) ≤ val WuPaper.ClassicalFourthData.Bq 1508
    have hp : val WuPaper.ClassicalFourthData.Bq 1508 = (134584442468035:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1508 = 134584442468035 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1508 = (2377:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1508
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1509) ≤ val WuPaper.ClassicalFourthData.Bq 1509
    have hp : val WuPaper.ClassicalFourthData.Bq 1509 = (134646653642103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1509 = 134646653642103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1509 = (9509:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1509
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1510) ≤ val WuPaper.ClassicalFourthData.Bq 1510
    have hp : val WuPaper.ClassicalFourthData.Bq 1510 = (134708837873789:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1510 = 134708837873789 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1510 = (951:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1510
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1511) ≤ val WuPaper.ClassicalFourthData.Bq 1511
    have hp : val WuPaper.ClassicalFourthData.Bq 1511 = (134770995176620:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1511 = 134770995176620 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1511 = (9511:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1511
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1512) ≤ val WuPaper.ClassicalFourthData.Bq 1512
    have hp : val WuPaper.ClassicalFourthData.Bq 1512 = (134833125564116:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1512 = 134833125564116 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1512 = (1189:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1512
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1513) ≤ val WuPaper.ClassicalFourthData.Bq 1513
    have hp : val WuPaper.ClassicalFourthData.Bq 1513 = (134895229049787:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1513 = 134895229049787 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1513 = (9513:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1513
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1514) ≤ val WuPaper.ClassicalFourthData.Bq 1514
    have hp : val WuPaper.ClassicalFourthData.Bq 1514 = (134957305647137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1514 = 134957305647137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1514 = (4757:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1514
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1515) ≤ val WuPaper.ClassicalFourthData.Bq 1515
    have hp : val WuPaper.ClassicalFourthData.Bq 1515 = (135019355369659:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1515 = 135019355369659 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1515 = (1903:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1515
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1516) ≤ val WuPaper.ClassicalFourthData.Bq 1516
    have hp : val WuPaper.ClassicalFourthData.Bq 1516 = (135081378230839:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1516 = 135081378230839 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1516 = (2379:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1516
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1517) ≤ val WuPaper.ClassicalFourthData.Bq 1517
    have hp : val WuPaper.ClassicalFourthData.Bq 1517 = (135143374244154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1517 = 135143374244154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1517 = (9517:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1517
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1518) ≤ val WuPaper.ClassicalFourthData.Bq 1518
    have hp : val WuPaper.ClassicalFourthData.Bq 1518 = (135205343423074:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1518 = 135205343423074 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1518 = (4759:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1518
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1519) ≤ val WuPaper.ClassicalFourthData.Bq 1519
    have hp : val WuPaper.ClassicalFourthData.Bq 1519 = (135267285781059:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1519 = 135267285781059 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1519 = (9519:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1519
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_094
