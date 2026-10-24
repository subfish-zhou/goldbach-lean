import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints406
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_406 (j : Fin 16) (hj : 16*406+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*406+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*406+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6496) ≤ val WuPaper.ClassicalFourthData.Bq 6496
    have hp : val WuPaper.ClassicalFourthData.Bq 6496 = (266197536170506:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6496 = 266197536170506 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6496 = (453:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6496
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6497) ≤ val WuPaper.ClassicalFourthData.Bq 6497
    have hp : val WuPaper.ClassicalFourthData.Bq 6497 = (266205460697756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6497 = 266205460697756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6497 = (14497:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6497
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6498) ≤ val WuPaper.ClassicalFourthData.Bq 6498
    have hp : val WuPaper.ClassicalFourthData.Bq 6498 = (266213381627890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6498 = 266213381627890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6498 = (7249:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6498
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6499) ≤ val WuPaper.ClassicalFourthData.Bq 6499
    have hp : val WuPaper.ClassicalFourthData.Bq 6499 = (266221298962131:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6499 = 266221298962131 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6499 = (14499:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6499
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6500) ≤ val WuPaper.ClassicalFourthData.Bq 6500
    have hp : val WuPaper.ClassicalFourthData.Bq 6500 = (266229212701699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6500 = 266229212701699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6500 = (29:ℝ)/8 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6500
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6501) ≤ val WuPaper.ClassicalFourthData.Bq 6501
    have hp : val WuPaper.ClassicalFourthData.Bq 6501 = (266237122847814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6501 = 266237122847814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6501 = (14501:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6501
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6502) ≤ val WuPaper.ClassicalFourthData.Bq 6502
    have hp : val WuPaper.ClassicalFourthData.Bq 6502 = (266245029401696:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6502 = 266245029401696 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6502 = (7251:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6502
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6503) ≤ val WuPaper.ClassicalFourthData.Bq 6503
    have hp : val WuPaper.ClassicalFourthData.Bq 6503 = (266252932364564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6503 = 266252932364564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6503 = (14503:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6503
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6504) ≤ val WuPaper.ClassicalFourthData.Bq 6504
    have hp : val WuPaper.ClassicalFourthData.Bq 6504 = (266260831737638:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6504 = 266260831737638 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6504 = (1813:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6504
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6505) ≤ val WuPaper.ClassicalFourthData.Bq 6505
    have hp : val WuPaper.ClassicalFourthData.Bq 6505 = (266268727522136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6505 = 266268727522136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6505 = (2901:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6505
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6506) ≤ val WuPaper.ClassicalFourthData.Bq 6506
    have hp : val WuPaper.ClassicalFourthData.Bq 6506 = (266276619719275:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6506 = 266276619719275 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6506 = (7253:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6506
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6507) ≤ val WuPaper.ClassicalFourthData.Bq 6507
    have hp : val WuPaper.ClassicalFourthData.Bq 6507 = (266284508330274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6507 = 266284508330274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6507 = (14507:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6507
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6508) ≤ val WuPaper.ClassicalFourthData.Bq 6508
    have hp : val WuPaper.ClassicalFourthData.Bq 6508 = (266292393356348:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6508 = 266292393356348 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6508 = (3627:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6508
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6509) ≤ val WuPaper.ClassicalFourthData.Bq 6509
    have hp : val WuPaper.ClassicalFourthData.Bq 6509 = (266300274798716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6509 = 266300274798716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6509 = (14509:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6509
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6510) ≤ val WuPaper.ClassicalFourthData.Bq 6510
    have hp : val WuPaper.ClassicalFourthData.Bq 6510 = (266308152658592:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6510 = 266308152658592 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6510 = (1451:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6510
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6511) ≤ val WuPaper.ClassicalFourthData.Bq 6511
    have hp : val WuPaper.ClassicalFourthData.Bq 6511 = (266316026937192:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6511 = 266316026937192 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6511 = (14511:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_406
