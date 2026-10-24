import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints157
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_157 (j : Fin 16) (hj : 16*157+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*157+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*157+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2512) ≤ val WuPaper.ClassicalFourthData.Bq 2512
    have hp : val WuPaper.ClassicalFourthData.Bq 2512 = (185446068333466:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2512 = 185446068333466 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2512 = (657:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2512
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2513) ≤ val WuPaper.ClassicalFourthData.Bq 2513
    have hp : val WuPaper.ClassicalFourthData.Bq 2513 = (185486851876486:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2513 = 185486851876486 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2513 = (10513:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2513
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2514) ≤ val WuPaper.ClassicalFourthData.Bq 2514
    have hp : val WuPaper.ClassicalFourthData.Bq 2514 = (185527618692849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2514 = 185527618692849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2514 = (5257:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2514
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2515) ≤ val WuPaper.ClassicalFourthData.Bq 2515
    have hp : val WuPaper.ClassicalFourthData.Bq 2515 = (185568368790079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2515 = 185568368790079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2515 = (2103:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2515
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2516) ≤ val WuPaper.ClassicalFourthData.Bq 2516
    have hp : val WuPaper.ClassicalFourthData.Bq 2516 = (185609102175698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2516 = 185609102175698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2516 = (2629:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2516
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2517) ≤ val WuPaper.ClassicalFourthData.Bq 2517
    have hp : val WuPaper.ClassicalFourthData.Bq 2517 = (185649818857223:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2517 = 185649818857223 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2517 = (10517:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2517
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2518) ≤ val WuPaper.ClassicalFourthData.Bq 2518
    have hp : val WuPaper.ClassicalFourthData.Bq 2518 = (185690518842168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2518 = 185690518842168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2518 = (5259:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2518
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2519) ≤ val WuPaper.ClassicalFourthData.Bq 2519
    have hp : val WuPaper.ClassicalFourthData.Bq 2519 = (185731202138041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2519 = 185731202138041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2519 = (10519:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2519
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2520) ≤ val WuPaper.ClassicalFourthData.Bq 2520
    have hp : val WuPaper.ClassicalFourthData.Bq 2520 = (185771868752347:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2520 = 185771868752347 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2520 = (263:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2520
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2521) ≤ val WuPaper.ClassicalFourthData.Bq 2521
    have hp : val WuPaper.ClassicalFourthData.Bq 2521 = (185812518692587:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2521 = 185812518692587 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2521 = (10521:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2521
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2522) ≤ val WuPaper.ClassicalFourthData.Bq 2522
    have hp : val WuPaper.ClassicalFourthData.Bq 2522 = (185853151966257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2522 = 185853151966257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2522 = (5261:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2522
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2523) ≤ val WuPaper.ClassicalFourthData.Bq 2523
    have hp : val WuPaper.ClassicalFourthData.Bq 2523 = (185893768580849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2523 = 185893768580849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2523 = (10523:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2523
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2524) ≤ val WuPaper.ClassicalFourthData.Bq 2524
    have hp : val WuPaper.ClassicalFourthData.Bq 2524 = (185934368543853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2524 = 185934368543853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2524 = (2631:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2524
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2525) ≤ val WuPaper.ClassicalFourthData.Bq 2525
    have hp : val WuPaper.ClassicalFourthData.Bq 2525 = (185974951862753:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2525 = 185974951862753 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2525 = (421:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2525
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2526) ≤ val WuPaper.ClassicalFourthData.Bq 2526
    have hp : val WuPaper.ClassicalFourthData.Bq 2526 = (186015518545027:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2526 = 186015518545027 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2526 = (5263:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2526
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2527) ≤ val WuPaper.ClassicalFourthData.Bq 2527
    have hp : val WuPaper.ClassicalFourthData.Bq 2527 = (186056068598154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2527 = 186056068598154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2527 = (10527:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2527
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_157
