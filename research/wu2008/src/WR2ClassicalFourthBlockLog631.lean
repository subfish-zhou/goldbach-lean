import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints631
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_631 (j : Fin 16) (hj : 16*631+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*631+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*631+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10096) ≤ val WuPaper.ClassicalFourthData.Bq 10096
    have hp : val WuPaper.ClassicalFourthData.Bq 10096 = (278425443895762:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10096 = 278425443895762 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10096 = (1131:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10096
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10097) ≤ val WuPaper.ClassicalFourthData.Bq 10097
    have hp : val WuPaper.ClassicalFourthData.Bq 10097 = (278425738581989:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10097 = 278425738581989 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10097 = (18097:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10097
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10098) ≤ val WuPaper.ClassicalFourthData.Bq 10098
    have hp : val WuPaper.ClassicalFourthData.Bq 10098 = (278426032123467:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10098 = 278426032123467 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10098 = (9049:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10098
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10099) ≤ val WuPaper.ClassicalFourthData.Bq 10099
    have hp : val WuPaper.ClassicalFourthData.Bq 10099 = (278426324520546:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10099 = 278426324520546 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10099 = (18099:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10099
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10100) ≤ val WuPaper.ClassicalFourthData.Bq 10100
    have hp : val WuPaper.ClassicalFourthData.Bq 10100 = (278426615773571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10100 = 278426615773571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10100 = (181:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10100
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10101) ≤ val WuPaper.ClassicalFourthData.Bq 10101
    have hp : val WuPaper.ClassicalFourthData.Bq 10101 = (278426905882891:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10101 = 278426905882891 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10101 = (18101:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10101
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10102) ≤ val WuPaper.ClassicalFourthData.Bq 10102
    have hp : val WuPaper.ClassicalFourthData.Bq 10102 = (278427194848852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10102 = 278427194848852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10102 = (9051:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10102
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10103) ≤ val WuPaper.ClassicalFourthData.Bq 10103
    have hp : val WuPaper.ClassicalFourthData.Bq 10103 = (278427482671801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10103 = 278427482671801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10103 = (18103:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10103
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10104) ≤ val WuPaper.ClassicalFourthData.Bq 10104
    have hp : val WuPaper.ClassicalFourthData.Bq 10104 = (278427769352086:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10104 = 278427769352086 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10104 = (2263:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10104
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10105) ≤ val WuPaper.ClassicalFourthData.Bq 10105
    have hp : val WuPaper.ClassicalFourthData.Bq 10105 = (278428054890053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10105 = 278428054890053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10105 = (3621:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10105
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10106) ≤ val WuPaper.ClassicalFourthData.Bq 10106
    have hp : val WuPaper.ClassicalFourthData.Bq 10106 = (278428339286050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10106 = 278428339286050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10106 = (9053:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10106
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10107) ≤ val WuPaper.ClassicalFourthData.Bq 10107
    have hp : val WuPaper.ClassicalFourthData.Bq 10107 = (278428622540422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10107 = 278428622540422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10107 = (18107:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10107
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10108) ≤ val WuPaper.ClassicalFourthData.Bq 10108
    have hp : val WuPaper.ClassicalFourthData.Bq 10108 = (278428904653516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10108 = 278428904653516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10108 = (4527:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10108
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10109) ≤ val WuPaper.ClassicalFourthData.Bq 10109
    have hp : val WuPaper.ClassicalFourthData.Bq 10109 = (278429185625679:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10109 = 278429185625679 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10109 = (18109:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10109
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10110) ≤ val WuPaper.ClassicalFourthData.Bq 10110
    have hp : val WuPaper.ClassicalFourthData.Bq 10110 = (278429465457257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10110 = 278429465457257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10110 = (1811:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10110
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10111) ≤ val WuPaper.ClassicalFourthData.Bq 10111
    have hp : val WuPaper.ClassicalFourthData.Bq 10111 = (278429744148596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10111 = 278429744148596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10111 = (18111:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_631
