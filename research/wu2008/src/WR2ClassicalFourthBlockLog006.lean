import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints006
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_006 (j : Fin 16) (hj : 16*6+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*6+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*6+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 96) ≤ val WuPaper.ClassicalFourthData.Bq 96
    have hp : val WuPaper.ClassicalFourthData.Bq 96 = (11717651490769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 96 = 11717651490769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 96 = (253:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_96
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 97) ≤ val WuPaper.ClassicalFourthData.Bq 97
    have hp : val WuPaper.ClassicalFourthData.Bq 97 = (11836797552103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 97 = 11836797552103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 97 = (8097:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_97
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 98) ≤ val WuPaper.ClassicalFourthData.Bq 98
    have hp : val WuPaper.ClassicalFourthData.Bq 98 = (11955884760098:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 98 = 11955884760098 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 98 = (4049:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_98
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 99) ≤ val WuPaper.ClassicalFourthData.Bq 99
    have hp : val WuPaper.ClassicalFourthData.Bq 99 = (12074913150913:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 99 = 12074913150913 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 99 = (8099:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_99
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 100) ≤ val WuPaper.ClassicalFourthData.Bq 100
    have hp : val WuPaper.ClassicalFourthData.Bq 100 = (12193882760678:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 100 = 12193882760678 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 100 = (81:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_100
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 101) ≤ val WuPaper.ClassicalFourthData.Bq 101
    have hp : val WuPaper.ClassicalFourthData.Bq 101 = (12312793625494:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 101 = 12312793625494 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 101 = (8101:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_101
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 102) ≤ val WuPaper.ClassicalFourthData.Bq 102
    have hp : val WuPaper.ClassicalFourthData.Bq 102 = (12431645781436:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 102 = 12431645781436 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 102 = (4051:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_102
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 103) ≤ val WuPaper.ClassicalFourthData.Bq 103
    have hp : val WuPaper.ClassicalFourthData.Bq 103 = (12550439264549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 103 = 12550439264549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 103 = (8103:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_103
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 104) ≤ val WuPaper.ClassicalFourthData.Bq 104
    have hp : val WuPaper.ClassicalFourthData.Bq 104 = (12669174110848:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 104 = 12669174110848 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 104 = (1013:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_104
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 105) ≤ val WuPaper.ClassicalFourthData.Bq 105
    have hp : val WuPaper.ClassicalFourthData.Bq 105 = (12787850356324:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 105 = 12787850356324 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 105 = (1621:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_105
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 106) ≤ val WuPaper.ClassicalFourthData.Bq 106
    have hp : val WuPaper.ClassicalFourthData.Bq 106 = (12906468036937:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 106 = 12906468036937 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 106 = (4053:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_106
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 107) ≤ val WuPaper.ClassicalFourthData.Bq 107
    have hp : val WuPaper.ClassicalFourthData.Bq 107 = (13025027188618:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 107 = 13025027188618 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 107 = (8107:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_107
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 108) ≤ val WuPaper.ClassicalFourthData.Bq 108
    have hp : val WuPaper.ClassicalFourthData.Bq 108 = (13143527847273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 108 = 13143527847273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 108 = (2027:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_108
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 109) ≤ val WuPaper.ClassicalFourthData.Bq 109
    have hp : val WuPaper.ClassicalFourthData.Bq 109 = (13261970048777:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 109 = 13261970048777 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 109 = (8109:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_109
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 110) ≤ val WuPaper.ClassicalFourthData.Bq 110
    have hp : val WuPaper.ClassicalFourthData.Bq 110 = (13380353828978:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 110 = 13380353828978 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 110 = (811:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_110
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 111) ≤ val WuPaper.ClassicalFourthData.Bq 111
    have hp : val WuPaper.ClassicalFourthData.Bq 111 = (13498679223697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 111 = 13498679223697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 111 = (8111:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_006
