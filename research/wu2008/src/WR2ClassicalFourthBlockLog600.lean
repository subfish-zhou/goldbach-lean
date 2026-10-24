import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints600
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_600 (j : Fin 16) (hj : 16*600+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*600+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*600+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9600) ≤ val WuPaper.ClassicalFourthData.Bq 9600
    have hp : val WuPaper.ClassicalFourthData.Bq 9600 = (278130779925511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9600 = 278130779925511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9600 = (22:ℝ)/5 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9600
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9601) ≤ val WuPaper.ClassicalFourthData.Bq 9601
    have hp : val WuPaper.ClassicalFourthData.Bq 9601 = (278131687604328:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9601 = 278131687604328 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9601 = (17601:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9601
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9602) ≤ val WuPaper.ClassicalFourthData.Bq 9602
    have hp : val WuPaper.ClassicalFourthData.Bq 9602 = (278132593951564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9602 = 278132593951564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9602 = (8801:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9602
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9603) ≤ val WuPaper.ClassicalFourthData.Bq 9603
    have hp : val WuPaper.ClassicalFourthData.Bq 9603 = (278133498967627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9603 = 278133498967627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9603 = (17603:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9603
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9604) ≤ val WuPaper.ClassicalFourthData.Bq 9604
    have hp : val WuPaper.ClassicalFourthData.Bq 9604 = (278134402652925:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9604 = 278134402652925 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9604 = (4401:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9604
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9605) ≤ val WuPaper.ClassicalFourthData.Bq 9605
    have hp : val WuPaper.ClassicalFourthData.Bq 9605 = (278135305007866:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9605 = 278135305007866 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9605 = (3521:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9605
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9606) ≤ val WuPaper.ClassicalFourthData.Bq 9606
    have hp : val WuPaper.ClassicalFourthData.Bq 9606 = (278136206032855:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9606 = 278136206032855 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9606 = (8803:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9606
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9607) ≤ val WuPaper.ClassicalFourthData.Bq 9607
    have hp : val WuPaper.ClassicalFourthData.Bq 9607 = (278137105728300:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9607 = 278137105728300 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9607 = (17607:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9607
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9608) ≤ val WuPaper.ClassicalFourthData.Bq 9608
    have hp : val WuPaper.ClassicalFourthData.Bq 9608 = (278138004094609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9608 = 278138004094609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9608 = (2201:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9608
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9609) ≤ val WuPaper.ClassicalFourthData.Bq 9609
    have hp : val WuPaper.ClassicalFourthData.Bq 9609 = (278138901132188:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9609 = 278138901132188 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9609 = (17609:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9609
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9610) ≤ val WuPaper.ClassicalFourthData.Bq 9610
    have hp : val WuPaper.ClassicalFourthData.Bq 9610 = (278139796841443:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9610 = 278139796841443 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9610 = (1761:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9610
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9611) ≤ val WuPaper.ClassicalFourthData.Bq 9611
    have hp : val WuPaper.ClassicalFourthData.Bq 9611 = (278140691222781:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9611 = 278140691222781 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9611 = (17611:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9611
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9612) ≤ val WuPaper.ClassicalFourthData.Bq 9612
    have hp : val WuPaper.ClassicalFourthData.Bq 9612 = (278141584276608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9612 = 278141584276608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9612 = (4403:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9612
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9613) ≤ val WuPaper.ClassicalFourthData.Bq 9613
    have hp : val WuPaper.ClassicalFourthData.Bq 9613 = (278142476003330:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9613 = 278142476003330 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9613 = (17613:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9613
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9614) ≤ val WuPaper.ClassicalFourthData.Bq 9614
    have hp : val WuPaper.ClassicalFourthData.Bq 9614 = (278143366403355:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9614 = 278143366403355 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9614 = (8807:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9614
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9615) ≤ val WuPaper.ClassicalFourthData.Bq 9615
    have hp : val WuPaper.ClassicalFourthData.Bq 9615 = (278144255477087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9615 = 278144255477087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9615 = (3523:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9615
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_600
