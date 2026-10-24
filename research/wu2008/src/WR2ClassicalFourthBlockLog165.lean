import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints165
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_165 (j : Fin 16) (hj : 16*165+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*165+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*165+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2640) ≤ val WuPaper.ClassicalFourthData.Bq 2640
    have hp : val WuPaper.ClassicalFourthData.Bq 2640 = (190532933221223:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2640 = 190532933221223 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2640 = (133:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2640
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2641) ≤ val WuPaper.ClassicalFourthData.Bq 2641
    have hp : val WuPaper.ClassicalFourthData.Bq 2641 = (190571635537520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2641 = 190571635537520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2641 = (10641:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2641
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2642) ≤ val WuPaper.ClassicalFourthData.Bq 2642
    have hp : val WuPaper.ClassicalFourthData.Bq 2642 = (190610322057758:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2642 = 190610322057758 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2642 = (5321:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2642
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2643) ≤ val WuPaper.ClassicalFourthData.Bq 2643
    have hp : val WuPaper.ClassicalFourthData.Bq 2643 = (190648992788956:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2643 = 190648992788956 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2643 = (10643:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2643
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2644) ≤ val WuPaper.ClassicalFourthData.Bq 2644
    have hp : val WuPaper.ClassicalFourthData.Bq 2644 = (190687647738128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2644 = 190687647738128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2644 = (2661:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2644
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2645) ≤ val WuPaper.ClassicalFourthData.Bq 2645
    have hp : val WuPaper.ClassicalFourthData.Bq 2645 = (190726286912285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2645 = 190726286912285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2645 = (2129:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2645
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2646) ≤ val WuPaper.ClassicalFourthData.Bq 2646
    have hp : val WuPaper.ClassicalFourthData.Bq 2646 = (190764910318434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2646 = 190764910318434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2646 = (5323:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2646
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2647) ≤ val WuPaper.ClassicalFourthData.Bq 2647
    have hp : val WuPaper.ClassicalFourthData.Bq 2647 = (190803517963579:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2647 = 190803517963579 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2647 = (10647:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2647
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2648) ≤ val WuPaper.ClassicalFourthData.Bq 2648
    have hp : val WuPaper.ClassicalFourthData.Bq 2648 = (190842109854717:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2648 = 190842109854717 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2648 = (1331:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2648
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2649) ≤ val WuPaper.ClassicalFourthData.Bq 2649
    have hp : val WuPaper.ClassicalFourthData.Bq 2649 = (190880685998846:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2649 = 190880685998846 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2649 = (10649:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2649
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2650) ≤ val WuPaper.ClassicalFourthData.Bq 2650
    have hp : val WuPaper.ClassicalFourthData.Bq 2650 = (190919246402957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2650 = 190919246402957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2650 = (213:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2650
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2651) ≤ val WuPaper.ClassicalFourthData.Bq 2651
    have hp : val WuPaper.ClassicalFourthData.Bq 2651 = (190957791074038:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2651 = 190957791074038 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2651 = (10651:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2651
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2652) ≤ val WuPaper.ClassicalFourthData.Bq 2652
    have hp : val WuPaper.ClassicalFourthData.Bq 2652 = (190996320019073:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2652 = 190996320019073 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2652 = (2663:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2652
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2653) ≤ val WuPaper.ClassicalFourthData.Bq 2653
    have hp : val WuPaper.ClassicalFourthData.Bq 2653 = (191034833245043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2653 = 191034833245043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2653 = (10653:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2653
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2654) ≤ val WuPaper.ClassicalFourthData.Bq 2654
    have hp : val WuPaper.ClassicalFourthData.Bq 2654 = (191073330758925:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2654 = 191073330758925 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2654 = (5327:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2654
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2655) ≤ val WuPaper.ClassicalFourthData.Bq 2655
    have hp : val WuPaper.ClassicalFourthData.Bq 2655 = (191111812567691:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2655 = 191111812567691 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2655 = (2131:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2655
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_165
