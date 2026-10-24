import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints358
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_358 (j : Fin 16) (hj : 16*358+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*358+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*358+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5728) ≤ val WuPaper.ClassicalFourthData.Bq 5728
    have hp : val WuPaper.ClassicalFourthData.Bq 5728 = (258949290240073:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5728 = 258949290240073 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5728 = (429:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5728
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5729) ≤ val WuPaper.ClassicalFourthData.Bq 5729
    have hp : val WuPaper.ClassicalFourthData.Bq 5729 = (258960377266635:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5729 = 258960377266635 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5729 = (13729:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5729
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5730) ≤ val WuPaper.ClassicalFourthData.Bq 5730
    have hp : val WuPaper.ClassicalFourthData.Bq 5730 = (258971459600301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5730 = 258971459600301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5730 = (1373:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5730
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5731) ≤ val WuPaper.ClassicalFourthData.Bq 5731
    have hp : val WuPaper.ClassicalFourthData.Bq 5731 = (258982537242727:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5731 = 258982537242727 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5731 = (13731:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5731
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5732) ≤ val WuPaper.ClassicalFourthData.Bq 5732
    have hp : val WuPaper.ClassicalFourthData.Bq 5732 = (258993610195571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5732 = 258993610195571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5732 = (3433:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5732
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5733) ≤ val WuPaper.ClassicalFourthData.Bq 5733
    have hp : val WuPaper.ClassicalFourthData.Bq 5733 = (259004678460489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5733 = 259004678460489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5733 = (13733:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5733
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5734) ≤ val WuPaper.ClassicalFourthData.Bq 5734
    have hp : val WuPaper.ClassicalFourthData.Bq 5734 = (259015742039138:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5734 = 259015742039138 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5734 = (6867:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5734
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5735) ≤ val WuPaper.ClassicalFourthData.Bq 5735
    have hp : val WuPaper.ClassicalFourthData.Bq 5735 = (259026800933173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5735 = 259026800933173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5735 = (2747:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5735
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5736) ≤ val WuPaper.ClassicalFourthData.Bq 5736
    have hp : val WuPaper.ClassicalFourthData.Bq 5736 = (259037855144247:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5736 = 259037855144247 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5736 = (1717:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5736
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5737) ≤ val WuPaper.ClassicalFourthData.Bq 5737
    have hp : val WuPaper.ClassicalFourthData.Bq 5737 = (259048904674015:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5737 = 259048904674015 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5737 = (13737:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5737
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5738) ≤ val WuPaper.ClassicalFourthData.Bq 5738
    have hp : val WuPaper.ClassicalFourthData.Bq 5738 = (259059949524131:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5738 = 259059949524131 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5738 = (6869:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5738
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5739) ≤ val WuPaper.ClassicalFourthData.Bq 5739
    have hp : val WuPaper.ClassicalFourthData.Bq 5739 = (259070989696246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5739 = 259070989696246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5739 = (13739:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5739
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5740) ≤ val WuPaper.ClassicalFourthData.Bq 5740
    have hp : val WuPaper.ClassicalFourthData.Bq 5740 = (259082025192012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5740 = 259082025192012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5740 = (687:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5740
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5741) ≤ val WuPaper.ClassicalFourthData.Bq 5741
    have hp : val WuPaper.ClassicalFourthData.Bq 5741 = (259093056013081:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5741 = 259093056013081 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5741 = (13741:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5741
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5742) ≤ val WuPaper.ClassicalFourthData.Bq 5742
    have hp : val WuPaper.ClassicalFourthData.Bq 5742 = (259104082161103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5742 = 259104082161103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5742 = (6871:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5742
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5743) ≤ val WuPaper.ClassicalFourthData.Bq 5743
    have hp : val WuPaper.ClassicalFourthData.Bq 5743 = (259115103637728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5743 = 259115103637728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5743 = (13743:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5743
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_358
