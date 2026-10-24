import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints546
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_546 (j : Fin 16) (hj : 16*546+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*546+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*546+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8736) ≤ val WuPaper.ClassicalFourthData.Bq 8736
    have hp : val WuPaper.ClassicalFourthData.Bq 8736 = (276801689290900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8736 = 276801689290900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8736 = (523:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8736
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8737) ≤ val WuPaper.ClassicalFourthData.Bq 8737
    have hp : val WuPaper.ClassicalFourthData.Bq 8737 = (276803915277228:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8737 = 276803915277228 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8737 = (16737:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8737
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8738) ≤ val WuPaper.ClassicalFourthData.Bq 8738
    have hp : val WuPaper.ClassicalFourthData.Bq 8738 = (276806139524511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8738 = 276806139524511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8738 = (8369:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8738
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8739) ≤ val WuPaper.ClassicalFourthData.Bq 8739
    have hp : val WuPaper.ClassicalFourthData.Bq 8739 = (276808362033290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8739 = 276808362033290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8739 = (16739:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8739
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8740) ≤ val WuPaper.ClassicalFourthData.Bq 8740
    have hp : val WuPaper.ClassicalFourthData.Bq 8740 = (276810582804110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8740 = 276810582804110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8740 = (837:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8740
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8741) ≤ val WuPaper.ClassicalFourthData.Bq 8741
    have hp : val WuPaper.ClassicalFourthData.Bq 8741 = (276812801837512:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8741 = 276812801837512 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8741 = (16741:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8741
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8742) ≤ val WuPaper.ClassicalFourthData.Bq 8742
    have hp : val WuPaper.ClassicalFourthData.Bq 8742 = (276815019134039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8742 = 276815019134039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8742 = (8371:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8742
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8743) ≤ val WuPaper.ClassicalFourthData.Bq 8743
    have hp : val WuPaper.ClassicalFourthData.Bq 8743 = (276817234694233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8743 = 276817234694233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8743 = (16743:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8743
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8744) ≤ val WuPaper.ClassicalFourthData.Bq 8744
    have hp : val WuPaper.ClassicalFourthData.Bq 8744 = (276819448518637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8744 = 276819448518637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8744 = (2093:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8744
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8745) ≤ val WuPaper.ClassicalFourthData.Bq 8745
    have hp : val WuPaper.ClassicalFourthData.Bq 8745 = (276821660607791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8745 = 276821660607791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8745 = (3349:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8745
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8746) ≤ val WuPaper.ClassicalFourthData.Bq 8746
    have hp : val WuPaper.ClassicalFourthData.Bq 8746 = (276823870962238:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8746 = 276823870962238 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8746 = (8373:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8746
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8747) ≤ val WuPaper.ClassicalFourthData.Bq 8747
    have hp : val WuPaper.ClassicalFourthData.Bq 8747 = (276826079582519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8747 = 276826079582519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8747 = (16747:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8747
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8748) ≤ val WuPaper.ClassicalFourthData.Bq 8748
    have hp : val WuPaper.ClassicalFourthData.Bq 8748 = (276828286469176:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8748 = 276828286469176 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8748 = (4187:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8748
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8749) ≤ val WuPaper.ClassicalFourthData.Bq 8749
    have hp : val WuPaper.ClassicalFourthData.Bq 8749 = (276830491622749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8749 = 276830491622749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8749 = (16749:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8749
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8750) ≤ val WuPaper.ClassicalFourthData.Bq 8750
    have hp : val WuPaper.ClassicalFourthData.Bq 8750 = (276832695043779:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8750 = 276832695043779 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8750 = (67:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8750
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8751) ≤ val WuPaper.ClassicalFourthData.Bq 8751
    have hp : val WuPaper.ClassicalFourthData.Bq 8751 = (276834896732808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8751 = 276834896732808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8751 = (16751:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8751
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_546
