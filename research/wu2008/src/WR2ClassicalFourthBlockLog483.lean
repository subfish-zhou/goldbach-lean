import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints483
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_483 (j : Fin 16) (hj : 16*483+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*483+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*483+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7728) ≤ val WuPaper.ClassicalFourthData.Bq 7728
    have hp : val WuPaper.ClassicalFourthData.Bq 7728 = (273571918623049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7728 = 273571918623049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7728 = (983:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7728
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7729) ≤ val WuPaper.ClassicalFourthData.Bq 7729
    have hp : val WuPaper.ClassicalFourthData.Bq 7729 = (273576208639050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7729 = 273576208639050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7729 = (15729:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7729
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7730) ≤ val WuPaper.ClassicalFourthData.Bq 7730
    have hp : val WuPaper.ClassicalFourthData.Bq 7730 = (273580496261137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7730 = 273580496261137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7730 = (1573:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7730
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7731) ≤ val WuPaper.ClassicalFourthData.Bq 7731
    have hp : val WuPaper.ClassicalFourthData.Bq 7731 = (273584781490083:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7731 = 273584781490083 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7731 = (15731:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7731
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7732) ≤ val WuPaper.ClassicalFourthData.Bq 7732
    have hp : val WuPaper.ClassicalFourthData.Bq 7732 = (273589064326659:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7732 = 273589064326659 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7732 = (3933:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7732
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7733) ≤ val WuPaper.ClassicalFourthData.Bq 7733
    have hp : val WuPaper.ClassicalFourthData.Bq 7733 = (273593344771635:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7733 = 273593344771635 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7733 = (15733:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7733
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7734) ≤ val WuPaper.ClassicalFourthData.Bq 7734
    have hp : val WuPaper.ClassicalFourthData.Bq 7734 = (273597622825783:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7734 = 273597622825783 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7734 = (7867:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7734
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7735) ≤ val WuPaper.ClassicalFourthData.Bq 7735
    have hp : val WuPaper.ClassicalFourthData.Bq 7735 = (273601898489874:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7735 = 273601898489874 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7735 = (3147:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7735
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7736) ≤ val WuPaper.ClassicalFourthData.Bq 7736
    have hp : val WuPaper.ClassicalFourthData.Bq 7736 = (273606171764676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7736 = 273606171764676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7736 = (1967:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7736
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7737) ≤ val WuPaper.ClassicalFourthData.Bq 7737
    have hp : val WuPaper.ClassicalFourthData.Bq 7737 = (273610442650962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7737 = 273610442650962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7737 = (15737:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7737
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7738) ≤ val WuPaper.ClassicalFourthData.Bq 7738
    have hp : val WuPaper.ClassicalFourthData.Bq 7738 = (273614711149499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7738 = 273614711149499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7738 = (7869:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7738
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7739) ≤ val WuPaper.ClassicalFourthData.Bq 7739
    have hp : val WuPaper.ClassicalFourthData.Bq 7739 = (273618977261059:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7739 = 273618977261059 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7739 = (15739:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7739
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7740) ≤ val WuPaper.ClassicalFourthData.Bq 7740
    have hp : val WuPaper.ClassicalFourthData.Bq 7740 = (273623240986409:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7740 = 273623240986409 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7740 = (787:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7740
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7741) ≤ val WuPaper.ClassicalFourthData.Bq 7741
    have hp : val WuPaper.ClassicalFourthData.Bq 7741 = (273627502326319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7741 = 273627502326319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7741 = (15741:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7741
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7742) ≤ val WuPaper.ClassicalFourthData.Bq 7742
    have hp : val WuPaper.ClassicalFourthData.Bq 7742 = (273631761281558:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7742 = 273631761281558 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7742 = (7871:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7742
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7743) ≤ val WuPaper.ClassicalFourthData.Bq 7743
    have hp : val WuPaper.ClassicalFourthData.Bq 7743 = (273636017852893:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7743 = 273636017852893 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7743 = (15743:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7743
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_483
