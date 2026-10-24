import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints091
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_091 (j : Fin 16) (hj : 16*91+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*91+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*91+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1456) ≤ val WuPaper.ClassicalFourthData.Bq 1456
    have hp : val WuPaper.ClassicalFourthData.Bq 1456 = (131311996371096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1456 = 131311996371096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1456 = (591:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1456
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1457) ≤ val WuPaper.ClassicalFourthData.Bq 1457
    have hp : val WuPaper.ClassicalFourthData.Bq 1457 = (131375627401588:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1457 = 131375627401588 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1457 = (9457:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1457
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1458) ≤ val WuPaper.ClassicalFourthData.Bq 1458
    have hp : val WuPaper.ClassicalFourthData.Bq 1458 = (131439230774480:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1458 = 131439230774480 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1458 = (4729:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1458
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1459) ≤ val WuPaper.ClassicalFourthData.Bq 1459
    have hp : val WuPaper.ClassicalFourthData.Bq 1459 = (131502806503745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1459 = 131502806503745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1459 = (9459:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1459
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1460) ≤ val WuPaper.ClassicalFourthData.Bq 1460
    have hp : val WuPaper.ClassicalFourthData.Bq 1460 = (131566354603351:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1460 = 131566354603351 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1460 = (473:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1460
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1461) ≤ val WuPaper.ClassicalFourthData.Bq 1461
    have hp : val WuPaper.ClassicalFourthData.Bq 1461 = (131629875087254:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1461 = 131629875087254 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1461 = (9461:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1461
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1462) ≤ val WuPaper.ClassicalFourthData.Bq 1462
    have hp : val WuPaper.ClassicalFourthData.Bq 1462 = (131693367969403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1462 = 131693367969403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1462 = (4731:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1462
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1463) ≤ val WuPaper.ClassicalFourthData.Bq 1463
    have hp : val WuPaper.ClassicalFourthData.Bq 1463 = (131756833263739:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1463 = 131756833263739 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1463 = (9463:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1463
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1464) ≤ val WuPaper.ClassicalFourthData.Bq 1464
    have hp : val WuPaper.ClassicalFourthData.Bq 1464 = (131820270984193:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1464 = 131820270984193 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1464 = (1183:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1464
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1465) ≤ val WuPaper.ClassicalFourthData.Bq 1465
    have hp : val WuPaper.ClassicalFourthData.Bq 1465 = (131883681144686:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1465 = 131883681144686 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1465 = (1893:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1465
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1466) ≤ val WuPaper.ClassicalFourthData.Bq 1466
    have hp : val WuPaper.ClassicalFourthData.Bq 1466 = (131947063759132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1466 = 131947063759132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1466 = (4733:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1466
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1467) ≤ val WuPaper.ClassicalFourthData.Bq 1467
    have hp : val WuPaper.ClassicalFourthData.Bq 1467 = (132010418841438:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1467 = 132010418841438 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1467 = (9467:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1467
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1468) ≤ val WuPaper.ClassicalFourthData.Bq 1468
    have hp : val WuPaper.ClassicalFourthData.Bq 1468 = (132073746405498:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1468 = 132073746405498 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1468 = (2367:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1468
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1469) ≤ val WuPaper.ClassicalFourthData.Bq 1469
    have hp : val WuPaper.ClassicalFourthData.Bq 1469 = (132137046465201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1469 = 132137046465201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1469 = (9469:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1469
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1470) ≤ val WuPaper.ClassicalFourthData.Bq 1470
    have hp : val WuPaper.ClassicalFourthData.Bq 1470 = (132200319034425:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1470 = 132200319034425 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1470 = (947:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1470
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1471) ≤ val WuPaper.ClassicalFourthData.Bq 1471
    have hp : val WuPaper.ClassicalFourthData.Bq 1471 = (132263564127040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1471 = 132263564127040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1471 = (9471:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1471
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_091
