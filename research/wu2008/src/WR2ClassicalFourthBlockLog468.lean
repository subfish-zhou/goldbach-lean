import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints468
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_468 (j : Fin 16) (hj : 16*468+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*468+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*468+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7488) ≤ val WuPaper.ClassicalFourthData.Bq 7488
    have hp : val WuPaper.ClassicalFourthData.Bq 7488 = (272471242558576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7488 = 272471242558576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7488 = (484:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7488
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7489) ≤ val WuPaper.ClassicalFourthData.Bq 7489
    have hp : val WuPaper.ClassicalFourthData.Bq 7489 = (272476130092884:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7489 = 272476130092884 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7489 = (15489:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7489
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7490) ≤ val WuPaper.ClassicalFourthData.Bq 7490
    have hp : val WuPaper.ClassicalFourthData.Bq 7490 = (272481015039795:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7490 = 272481015039795 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7490 = (1549:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7490
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7491) ≤ val WuPaper.ClassicalFourthData.Bq 7491
    have hp : val WuPaper.ClassicalFourthData.Bq 7491 = (272485897400153:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7491 = 272485897400153 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7491 = (15491:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7491
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7492) ≤ val WuPaper.ClassicalFourthData.Bq 7492
    have hp : val WuPaper.ClassicalFourthData.Bq 7492 = (272490777174797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7492 = 272490777174797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7492 = (3873:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7492
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7493) ≤ val WuPaper.ClassicalFourthData.Bq 7493
    have hp : val WuPaper.ClassicalFourthData.Bq 7493 = (272495654364570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7493 = 272495654364570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7493 = (15493:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7493
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7494) ≤ val WuPaper.ClassicalFourthData.Bq 7494
    have hp : val WuPaper.ClassicalFourthData.Bq 7494 = (272500528970311:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7494 = 272500528970311 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7494 = (7747:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7494
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7495) ≤ val WuPaper.ClassicalFourthData.Bq 7495
    have hp : val WuPaper.ClassicalFourthData.Bq 7495 = (272505400992862:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7495 = 272505400992862 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7495 = (3099:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7495
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7496) ≤ val WuPaper.ClassicalFourthData.Bq 7496
    have hp : val WuPaper.ClassicalFourthData.Bq 7496 = (272510270433061:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7496 = 272510270433061 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7496 = (1937:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7496
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7497) ≤ val WuPaper.ClassicalFourthData.Bq 7497
    have hp : val WuPaper.ClassicalFourthData.Bq 7497 = (272515137291749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7497 = 272515137291749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7497 = (15497:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7497
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7498) ≤ val WuPaper.ClassicalFourthData.Bq 7498
    have hp : val WuPaper.ClassicalFourthData.Bq 7498 = (272520001569766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7498 = 272520001569766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7498 = (7749:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7498
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7499) ≤ val WuPaper.ClassicalFourthData.Bq 7499
    have hp : val WuPaper.ClassicalFourthData.Bq 7499 = (272524863267950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7499 = 272524863267950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7499 = (15499:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7499
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7500) ≤ val WuPaper.ClassicalFourthData.Bq 7500
    have hp : val WuPaper.ClassicalFourthData.Bq 7500 = (272529722387140:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7500 = 272529722387140 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7500 = (31:ℝ)/8 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7500
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7501) ≤ val WuPaper.ClassicalFourthData.Bq 7501
    have hp : val WuPaper.ClassicalFourthData.Bq 7501 = (272534578928175:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7501 = 272534578928175 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7501 = (15501:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7501
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7502) ≤ val WuPaper.ClassicalFourthData.Bq 7502
    have hp : val WuPaper.ClassicalFourthData.Bq 7502 = (272539432891892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7502 = 272539432891892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7502 = (7751:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7502
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7503) ≤ val WuPaper.ClassicalFourthData.Bq 7503
    have hp : val WuPaper.ClassicalFourthData.Bq 7503 = (272544284279131:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7503 = 272544284279131 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7503 = (15503:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7503
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_468
