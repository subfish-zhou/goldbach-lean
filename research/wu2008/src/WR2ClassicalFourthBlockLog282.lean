import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints282
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_282 (j : Fin 16) (hj : 16*282+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*282+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*282+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4512) ≤ val WuPaper.ClassicalFourthData.Bq 4512
    have hp : val WuPaper.ClassicalFourthData.Bq 4512 = (241426653286253:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4512 = 241426653286253 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4512 = (391:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4512
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4513) ≤ val WuPaper.ClassicalFourthData.Bq 4513
    have hp : val WuPaper.ClassicalFourthData.Bq 4513 = (241444911941830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4513 = 241444911941830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4513 = (12513:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4513
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4514) ≤ val WuPaper.ClassicalFourthData.Bq 4514
    have hp : val WuPaper.ClassicalFourthData.Bq 4514 = (241463163268682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4514 = 241463163268682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4514 = (6257:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4514
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4515) ≤ val WuPaper.ClassicalFourthData.Bq 4515
    have hp : val WuPaper.ClassicalFourthData.Bq 4515 = (241481407269601:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4515 = 241481407269601 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4515 = (2503:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4515
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4516) ≤ val WuPaper.ClassicalFourthData.Bq 4516
    have hp : val WuPaper.ClassicalFourthData.Bq 4516 = (241499643947377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4516 = 241499643947377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4516 = (3129:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4516
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4517) ≤ val WuPaper.ClassicalFourthData.Bq 4517
    have hp : val WuPaper.ClassicalFourthData.Bq 4517 = (241517873304803:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4517 = 241517873304803 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4517 = (12517:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4517
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4518) ≤ val WuPaper.ClassicalFourthData.Bq 4518
    have hp : val WuPaper.ClassicalFourthData.Bq 4518 = (241536095344666:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4518 = 241536095344666 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4518 = (6259:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4518
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4519) ≤ val WuPaper.ClassicalFourthData.Bq 4519
    have hp : val WuPaper.ClassicalFourthData.Bq 4519 = (241554310069755:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4519 = 241554310069755 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4519 = (12519:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4519
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4520) ≤ val WuPaper.ClassicalFourthData.Bq 4520
    have hp : val WuPaper.ClassicalFourthData.Bq 4520 = (241572517482855:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4520 = 241572517482855 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4520 = (313:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4520
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4521) ≤ val WuPaper.ClassicalFourthData.Bq 4521
    have hp : val WuPaper.ClassicalFourthData.Bq 4521 = (241590717586752:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4521 = 241590717586752 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4521 = (12521:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4521
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4522) ≤ val WuPaper.ClassicalFourthData.Bq 4522
    have hp : val WuPaper.ClassicalFourthData.Bq 4522 = (241608910384230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4522 = 241608910384230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4522 = (6261:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4522
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4523) ≤ val WuPaper.ClassicalFourthData.Bq 4523
    have hp : val WuPaper.ClassicalFourthData.Bq 4523 = (241627095878071:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4523 = 241627095878071 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4523 = (12523:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4523
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4524) ≤ val WuPaper.ClassicalFourthData.Bq 4524
    have hp : val WuPaper.ClassicalFourthData.Bq 4524 = (241645274071058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4524 = 241645274071058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4524 = (3131:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4524
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4525) ≤ val WuPaper.ClassicalFourthData.Bq 4525
    have hp : val WuPaper.ClassicalFourthData.Bq 4525 = (241663444965969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4525 = 241663444965969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4525 = (501:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4525
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4526) ≤ val WuPaper.ClassicalFourthData.Bq 4526
    have hp : val WuPaper.ClassicalFourthData.Bq 4526 = (241681608565585:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4526 = 241681608565585 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4526 = (6263:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4526
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4527) ≤ val WuPaper.ClassicalFourthData.Bq 4527
    have hp : val WuPaper.ClassicalFourthData.Bq 4527 = (241699764872683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4527 = 241699764872683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4527 = (12527:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4527
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_282
