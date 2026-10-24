import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints093
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_093 (j : Fin 16) (hj : 16*93+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*93+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*93+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1488) ≤ val WuPaper.ClassicalFourthData.Bq 1488
    have hp : val WuPaper.ClassicalFourthData.Bq 1488 = (133334540178623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1488 = 133334540178623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1488 = (593:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1488
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1489) ≤ val WuPaper.ClassicalFourthData.Bq 1489
    have hp : val WuPaper.ClassicalFourthData.Bq 1489 = (133397293054216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1489 = 133397293054216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1489 = (9489:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1489
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1490) ≤ val WuPaper.ClassicalFourthData.Bq 1490
    have hp : val WuPaper.ClassicalFourthData.Bq 1490 = (133460018715089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1490 = 133460018715089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1490 = (949:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1490
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1491) ≤ val WuPaper.ClassicalFourthData.Bq 1491
    have hp : val WuPaper.ClassicalFourthData.Bq 1491 = (133522717174943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1491 = 133522717174943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1491 = (9491:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1491
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1492) ≤ val WuPaper.ClassicalFourthData.Bq 1492
    have hp : val WuPaper.ClassicalFourthData.Bq 1492 = (133585388447465:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1492 = 133585388447465 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1492 = (2373:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1492
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1493) ≤ val WuPaper.ClassicalFourthData.Bq 1493
    have hp : val WuPaper.ClassicalFourthData.Bq 1493 = (133648032546337:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1493 = 133648032546337 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1493 = (9493:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1493
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1494) ≤ val WuPaper.ClassicalFourthData.Bq 1494
    have hp : val WuPaper.ClassicalFourthData.Bq 1494 = (133710649485230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1494 = 133710649485230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1494 = (4747:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1494
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1495) ≤ val WuPaper.ClassicalFourthData.Bq 1495
    have hp : val WuPaper.ClassicalFourthData.Bq 1495 = (133773239277807:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1495 = 133773239277807 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1495 = (1899:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1495
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1496) ≤ val WuPaper.ClassicalFourthData.Bq 1496
    have hp : val WuPaper.ClassicalFourthData.Bq 1496 = (133835801937725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1496 = 133835801937725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1496 = (1187:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1496
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1497) ≤ val WuPaper.ClassicalFourthData.Bq 1497
    have hp : val WuPaper.ClassicalFourthData.Bq 1497 = (133898337478629:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1497 = 133898337478629 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1497 = (9497:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1497
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1498) ≤ val WuPaper.ClassicalFourthData.Bq 1498
    have hp : val WuPaper.ClassicalFourthData.Bq 1498 = (133960845914156:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1498 = 133960845914156 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1498 = (4749:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1498
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1499) ≤ val WuPaper.ClassicalFourthData.Bq 1499
    have hp : val WuPaper.ClassicalFourthData.Bq 1499 = (134023327257938:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1499 = 134023327257938 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1499 = (9499:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1499
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1500) ≤ val WuPaper.ClassicalFourthData.Bq 1500
    have hp : val WuPaper.ClassicalFourthData.Bq 1500 = (134085781523594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1500 = 134085781523594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1500 = (19:ℝ)/8 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1500
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1501) ≤ val WuPaper.ClassicalFourthData.Bq 1501
    have hp : val WuPaper.ClassicalFourthData.Bq 1501 = (134148208724737:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1501 = 134148208724737 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1501 = (9501:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1501
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1502) ≤ val WuPaper.ClassicalFourthData.Bq 1502
    have hp : val WuPaper.ClassicalFourthData.Bq 1502 = (134210608874971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1502 = 134210608874971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1502 = (4751:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1502
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1503) ≤ val WuPaper.ClassicalFourthData.Bq 1503
    have hp : val WuPaper.ClassicalFourthData.Bq 1503 = (134272981987891:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1503 = 134272981987891 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1503 = (9503:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1503
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_093
