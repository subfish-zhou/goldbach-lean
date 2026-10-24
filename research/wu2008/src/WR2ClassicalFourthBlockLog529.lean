import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints529
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_529 (j : Fin 16) (hj : 16*529+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*529+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*529+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8464) ≤ val WuPaper.ClassicalFourthData.Bq 8464
    have hp : val WuPaper.ClassicalFourthData.Bq 8464 = (276129768711136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8464 = 276129768711136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8464 = (1029:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8464
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8465) ≤ val WuPaper.ClassicalFourthData.Bq 8465
    have hp : val WuPaper.ClassicalFourthData.Bq 8465 = (276132488517990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8465 = 276132488517990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8465 = (3293:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8465
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8466) ≤ val WuPaper.ClassicalFourthData.Bq 8466
    have hp : val WuPaper.ClassicalFourthData.Bq 8466 = (276135206431028:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8466 = 276135206431028 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8466 = (8233:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8466
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8467) ≤ val WuPaper.ClassicalFourthData.Bq 8467
    have hp : val WuPaper.ClassicalFourthData.Bq 8467 = (276137922450846:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8467 = 276137922450846 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8467 = (16467:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8467
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8468) ≤ val WuPaper.ClassicalFourthData.Bq 8468
    have hp : val WuPaper.ClassicalFourthData.Bq 8468 = (276140636578039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8468 = 276140636578039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8468 = (4117:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8468
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8469) ≤ val WuPaper.ClassicalFourthData.Bq 8469
    have hp : val WuPaper.ClassicalFourthData.Bq 8469 = (276143348813202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8469 = 276143348813202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8469 = (16469:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8469
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8470) ≤ val WuPaper.ClassicalFourthData.Bq 8470
    have hp : val WuPaper.ClassicalFourthData.Bq 8470 = (276146059156932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8470 = 276146059156932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8470 = (1647:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8470
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8471) ≤ val WuPaper.ClassicalFourthData.Bq 8471
    have hp : val WuPaper.ClassicalFourthData.Bq 8471 = (276148767609822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8471 = 276148767609822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8471 = (16471:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8471
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8472) ≤ val WuPaper.ClassicalFourthData.Bq 8472
    have hp : val WuPaper.ClassicalFourthData.Bq 8472 = (276151474172468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8472 = 276151474172468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8472 = (2059:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8472
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8473) ≤ val WuPaper.ClassicalFourthData.Bq 8473
    have hp : val WuPaper.ClassicalFourthData.Bq 8473 = (276154178845464:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8473 = 276154178845464 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8473 = (16473:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8473
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8474) ≤ val WuPaper.ClassicalFourthData.Bq 8474
    have hp : val WuPaper.ClassicalFourthData.Bq 8474 = (276156881629405:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8474 = 276156881629405 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8474 = (8237:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8474
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8475) ≤ val WuPaper.ClassicalFourthData.Bq 8475
    have hp : val WuPaper.ClassicalFourthData.Bq 8475 = (276159582524884:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8475 = 276159582524884 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8475 = (659:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8475
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8476) ≤ val WuPaper.ClassicalFourthData.Bq 8476
    have hp : val WuPaper.ClassicalFourthData.Bq 8476 = (276162281532497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8476 = 276162281532497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8476 = (4119:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8476
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8477) ≤ val WuPaper.ClassicalFourthData.Bq 8477
    have hp : val WuPaper.ClassicalFourthData.Bq 8477 = (276164978652836:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8477 = 276164978652836 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8477 = (16477:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8477
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8478) ≤ val WuPaper.ClassicalFourthData.Bq 8478
    have hp : val WuPaper.ClassicalFourthData.Bq 8478 = (276167673886496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8478 = 276167673886496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8478 = (8239:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8478
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8479) ≤ val WuPaper.ClassicalFourthData.Bq 8479
    have hp : val WuPaper.ClassicalFourthData.Bq 8479 = (276170367234069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8479 = 276170367234069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8479 = (16479:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8479
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_529
