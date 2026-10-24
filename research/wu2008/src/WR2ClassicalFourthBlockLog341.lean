import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints341
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_341 (j : Fin 16) (hj : 16*341+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*341+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*341+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5456) ≤ val WuPaper.ClassicalFourthData.Bq 5456
    have hp : val WuPaper.ClassicalFourthData.Bq 5456 = (255753596772847:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5456 = 255753596772847 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5456 = (841:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5456
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5457) ≤ val WuPaper.ClassicalFourthData.Bq 5457
    have hp : val WuPaper.ClassicalFourthData.Bq 5457 = (255766024199595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5457 = 255766024199595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5457 = (13457:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5457
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5458) ≤ val WuPaper.ClassicalFourthData.Bq 5458
    have hp : val WuPaper.ClassicalFourthData.Bq 5458 = (255778446456174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5458 = 255778446456174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5458 = (6729:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5458
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5459) ≤ val WuPaper.ClassicalFourthData.Bq 5459
    have hp : val WuPaper.ClassicalFourthData.Bq 5459 = (255790863544438:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5459 = 255790863544438 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5459 = (13459:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5459
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5460) ≤ val WuPaper.ClassicalFourthData.Bq 5460
    have hp : val WuPaper.ClassicalFourthData.Bq 5460 = (255803275466241:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5460 = 255803275466241 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5460 = (673:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5460
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5461) ≤ val WuPaper.ClassicalFourthData.Bq 5461
    have hp : val WuPaper.ClassicalFourthData.Bq 5461 = (255815682223437:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5461 = 255815682223437 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5461 = (13461:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5461
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5462) ≤ val WuPaper.ClassicalFourthData.Bq 5462
    have hp : val WuPaper.ClassicalFourthData.Bq 5462 = (255828083817879:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5462 = 255828083817879 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5462 = (6731:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5462
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5463) ≤ val WuPaper.ClassicalFourthData.Bq 5463
    have hp : val WuPaper.ClassicalFourthData.Bq 5463 = (255840480251418:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5463 = 255840480251418 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5463 = (13463:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5463
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5464) ≤ val WuPaper.ClassicalFourthData.Bq 5464
    have hp : val WuPaper.ClassicalFourthData.Bq 5464 = (255852871525906:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5464 = 255852871525906 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5464 = (1683:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5464
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5465) ≤ val WuPaper.ClassicalFourthData.Bq 5465
    have hp : val WuPaper.ClassicalFourthData.Bq 5465 = (255865257643193:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5465 = 255865257643193 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5465 = (2693:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5465
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5466) ≤ val WuPaper.ClassicalFourthData.Bq 5466
    have hp : val WuPaper.ClassicalFourthData.Bq 5466 = (255877638605130:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5466 = 255877638605130 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5466 = (6733:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5466
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5467) ≤ val WuPaper.ClassicalFourthData.Bq 5467
    have hp : val WuPaper.ClassicalFourthData.Bq 5467 = (255890014413564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5467 = 255890014413564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5467 = (13467:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5467
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5468) ≤ val WuPaper.ClassicalFourthData.Bq 5468
    have hp : val WuPaper.ClassicalFourthData.Bq 5468 = (255902385070345:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5468 = 255902385070345 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5468 = (3367:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5468
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5469) ≤ val WuPaper.ClassicalFourthData.Bq 5469
    have hp : val WuPaper.ClassicalFourthData.Bq 5469 = (255914750577319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5469 = 255914750577319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5469 = (13469:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5469
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5470) ≤ val WuPaper.ClassicalFourthData.Bq 5470
    have hp : val WuPaper.ClassicalFourthData.Bq 5470 = (255927110936333:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5470 = 255927110936333 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5470 = (1347:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5470
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5471) ≤ val WuPaper.ClassicalFourthData.Bq 5471
    have hp : val WuPaper.ClassicalFourthData.Bq 5471 = (255939466149233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5471 = 255939466149233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5471 = (13471:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5471
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_341
