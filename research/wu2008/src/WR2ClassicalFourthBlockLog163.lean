import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints163
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_163 (j : Fin 16) (hj : 16*163+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*163+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*163+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2608) ≤ val WuPaper.ClassicalFourthData.Bq 2608
    have hp : val WuPaper.ClassicalFourthData.Bq 2608 = (189286076583253:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2608 = 189286076583253 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2608 = (663:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2608
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2609) ≤ val WuPaper.ClassicalFourthData.Bq 2609
    have hp : val WuPaper.ClassicalFourthData.Bq 2609 = (189325288101961:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2609 = 189325288101961 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2609 = (10609:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2609
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2610) ≤ val WuPaper.ClassicalFourthData.Bq 2610
    have hp : val WuPaper.ClassicalFourthData.Bq 2610 = (189364483598004:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2610 = 189364483598004 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2610 = (1061:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2610
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2611) ≤ val WuPaper.ClassicalFourthData.Bq 2611
    have hp : val WuPaper.ClassicalFourthData.Bq 2611 = (189403663078523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2611 = 189403663078523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2611 = (10611:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2611
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2612) ≤ val WuPaper.ClassicalFourthData.Bq 2612
    have hp : val WuPaper.ClassicalFourthData.Bq 2612 = (189442826550655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2612 = 189442826550655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2612 = (2653:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2612
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2613) ≤ val WuPaper.ClassicalFourthData.Bq 2613
    have hp : val WuPaper.ClassicalFourthData.Bq 2613 = (189481974021534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2613 = 189481974021534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2613 = (10613:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2613
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2614) ≤ val WuPaper.ClassicalFourthData.Bq 2614
    have hp : val WuPaper.ClassicalFourthData.Bq 2614 = (189521105498290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2614 = 189521105498290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2614 = (5307:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2614
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2615) ≤ val WuPaper.ClassicalFourthData.Bq 2615
    have hp : val WuPaper.ClassicalFourthData.Bq 2615 = (189560220988047:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2615 = 189560220988047 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2615 = (2123:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2615
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2616) ≤ val WuPaper.ClassicalFourthData.Bq 2616
    have hp : val WuPaper.ClassicalFourthData.Bq 2616 = (189599320497928:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2616 = 189599320497928 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2616 = (1327:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2616
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2617) ≤ val WuPaper.ClassicalFourthData.Bq 2617
    have hp : val WuPaper.ClassicalFourthData.Bq 2617 = (189638404035051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2617 = 189638404035051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2617 = (10617:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2617
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2618) ≤ val WuPaper.ClassicalFourthData.Bq 2618
    have hp : val WuPaper.ClassicalFourthData.Bq 2618 = (189677471606529:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2618 = 189677471606529 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2618 = (5309:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2618
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2619) ≤ val WuPaper.ClassicalFourthData.Bq 2619
    have hp : val WuPaper.ClassicalFourthData.Bq 2619 = (189716523219473:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2619 = 189716523219473 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2619 = (10619:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2619
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2620) ≤ val WuPaper.ClassicalFourthData.Bq 2620
    have hp : val WuPaper.ClassicalFourthData.Bq 2620 = (189755558880990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2620 = 189755558880990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2620 = (531:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2620
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2621) ≤ val WuPaper.ClassicalFourthData.Bq 2621
    have hp : val WuPaper.ClassicalFourthData.Bq 2621 = (189794578598181:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2621 = 189794578598181 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2621 = (10621:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2621
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2622) ≤ val WuPaper.ClassicalFourthData.Bq 2622
    have hp : val WuPaper.ClassicalFourthData.Bq 2622 = (189833582378145:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2622 = 189833582378145 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2622 = (5311:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2622
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2623) ≤ val WuPaper.ClassicalFourthData.Bq 2623
    have hp : val WuPaper.ClassicalFourthData.Bq 2623 = (189872570227978:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2623 = 189872570227978 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2623 = (10623:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2623
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_163
