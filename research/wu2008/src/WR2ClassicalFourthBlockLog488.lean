import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints488
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_488 (j : Fin 16) (hj : 16*488+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*488+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*488+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7808) ≤ val WuPaper.ClassicalFourthData.Bq 7808
    have hp : val WuPaper.ClassicalFourthData.Bq 7808 = (273907618102206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7808 = 273907618102206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7808 = (494:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7808
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7809) ≤ val WuPaper.ClassicalFourthData.Bq 7809
    have hp : val WuPaper.ClassicalFourthData.Bq 7809 = (273911719021052:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7809 = 273911719021052 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7809 = (15809:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7809
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7810) ≤ val WuPaper.ClassicalFourthData.Bq 7810
    have hp : val WuPaper.ClassicalFourthData.Bq 7810 = (273915817606852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7810 = 273915817606852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7810 = (1581:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7810
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7811) ≤ val WuPaper.ClassicalFourthData.Bq 7811
    have hp : val WuPaper.ClassicalFourthData.Bq 7811 = (273919913860357:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7811 = 273919913860357 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7811 = (15811:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7811
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7812) ≤ val WuPaper.ClassicalFourthData.Bq 7812
    have hp : val WuPaper.ClassicalFourthData.Bq 7812 = (273924007782316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7812 = 273924007782316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7812 = (3953:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7812
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7813) ≤ val WuPaper.ClassicalFourthData.Bq 7813
    have hp : val WuPaper.ClassicalFourthData.Bq 7813 = (273928099373479:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7813 = 273928099373479 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7813 = (15813:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7813
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7814) ≤ val WuPaper.ClassicalFourthData.Bq 7814
    have hp : val WuPaper.ClassicalFourthData.Bq 7814 = (273932188634594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7814 = 273932188634594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7814 = (7907:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7814
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7815) ≤ val WuPaper.ClassicalFourthData.Bq 7815
    have hp : val WuPaper.ClassicalFourthData.Bq 7815 = (273936275566412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7815 = 273936275566412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7815 = (3163:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7815
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7816) ≤ val WuPaper.ClassicalFourthData.Bq 7816
    have hp : val WuPaper.ClassicalFourthData.Bq 7816 = (273940360169679:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7816 = 273940360169679 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7816 = (1977:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7816
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7817) ≤ val WuPaper.ClassicalFourthData.Bq 7817
    have hp : val WuPaper.ClassicalFourthData.Bq 7817 = (273944442445145:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7817 = 273944442445145 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7817 = (15817:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7817
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7818) ≤ val WuPaper.ClassicalFourthData.Bq 7818
    have hp : val WuPaper.ClassicalFourthData.Bq 7818 = (273948522393557:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7818 = 273948522393557 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7818 = (7909:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7818
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7819) ≤ val WuPaper.ClassicalFourthData.Bq 7819
    have hp : val WuPaper.ClassicalFourthData.Bq 7819 = (273952600015664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7819 = 273952600015664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7819 = (15819:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7819
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7820) ≤ val WuPaper.ClassicalFourthData.Bq 7820
    have hp : val WuPaper.ClassicalFourthData.Bq 7820 = (273956675312212:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7820 = 273956675312212 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7820 = (791:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7820
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7821) ≤ val WuPaper.ClassicalFourthData.Bq 7821
    have hp : val WuPaper.ClassicalFourthData.Bq 7821 = (273960748283950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7821 = 273960748283950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7821 = (15821:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7821
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7822) ≤ val WuPaper.ClassicalFourthData.Bq 7822
    have hp : val WuPaper.ClassicalFourthData.Bq 7822 = (273964818931623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7822 = 273964818931623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7822 = (7911:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7822
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7823) ≤ val WuPaper.ClassicalFourthData.Bq 7823
    have hp : val WuPaper.ClassicalFourthData.Bq 7823 = (273968887255978:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7823 = 273968887255978 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7823 = (15823:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7823
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_488
