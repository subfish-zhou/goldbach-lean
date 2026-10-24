import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints508
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_508 (j : Fin 16) (hj : 16*508+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*508+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*508+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8128) ≤ val WuPaper.ClassicalFourthData.Bq 8128
    have hp : val WuPaper.ClassicalFourthData.Bq 8128 = (275104778716135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8128 = 275104778716135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8128 = (504:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8128
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8129) ≤ val WuPaper.ClassicalFourthData.Bq 8129
    have hp : val WuPaper.ClassicalFourthData.Bq 8129 = (275108169932467:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8129 = 275108169932467 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8129 = (16129:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8129
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8130) ≤ val WuPaper.ClassicalFourthData.Bq 8130
    have hp : val WuPaper.ClassicalFourthData.Bq 8130 = (275111559042632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8130 = 275111559042632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8130 = (1613:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8130
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8131) ≤ val WuPaper.ClassicalFourthData.Bq 8131
    have hp : val WuPaper.ClassicalFourthData.Bq 8131 = (275114946047299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8131 = 275114946047299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8131 = (16131:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8131
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8132) ≤ val WuPaper.ClassicalFourthData.Bq 8132
    have hp : val WuPaper.ClassicalFourthData.Bq 8132 = (275118330947137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8132 = 275118330947137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8132 = (4033:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8132
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8133) ≤ val WuPaper.ClassicalFourthData.Bq 8133
    have hp : val WuPaper.ClassicalFourthData.Bq 8133 = (275121713742816:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8133 = 275121713742816 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8133 = (16133:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8133
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8134) ≤ val WuPaper.ClassicalFourthData.Bq 8134
    have hp : val WuPaper.ClassicalFourthData.Bq 8134 = (275125094435004:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8134 = 275125094435004 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8134 = (8067:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8134
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8135) ≤ val WuPaper.ClassicalFourthData.Bq 8135
    have hp : val WuPaper.ClassicalFourthData.Bq 8135 = (275128473024370:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8135 = 275128473024370 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8135 = (3227:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8135
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8136) ≤ val WuPaper.ClassicalFourthData.Bq 8136
    have hp : val WuPaper.ClassicalFourthData.Bq 8136 = (275131849511583:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8136 = 275131849511583 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8136 = (2017:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8136
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8137) ≤ val WuPaper.ClassicalFourthData.Bq 8137
    have hp : val WuPaper.ClassicalFourthData.Bq 8137 = (275135223897311:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8137 = 275135223897311 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8137 = (16137:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8137
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8138) ≤ val WuPaper.ClassicalFourthData.Bq 8138
    have hp : val WuPaper.ClassicalFourthData.Bq 8138 = (275138596182222:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8138 = 275138596182222 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8138 = (8069:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8138
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8139) ≤ val WuPaper.ClassicalFourthData.Bq 8139
    have hp : val WuPaper.ClassicalFourthData.Bq 8139 = (275141966366983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8139 = 275141966366983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8139 = (16139:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8139
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8140) ≤ val WuPaper.ClassicalFourthData.Bq 8140
    have hp : val WuPaper.ClassicalFourthData.Bq 8140 = (275145334452262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8140 = 275145334452262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8140 = (807:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8140
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8141) ≤ val WuPaper.ClassicalFourthData.Bq 8141
    have hp : val WuPaper.ClassicalFourthData.Bq 8141 = (275148700438726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8141 = 275148700438726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8141 = (16141:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8141
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8142) ≤ val WuPaper.ClassicalFourthData.Bq 8142
    have hp : val WuPaper.ClassicalFourthData.Bq 8142 = (275152064327043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8142 = 275152064327043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8142 = (8071:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8142
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8143) ≤ val WuPaper.ClassicalFourthData.Bq 8143
    have hp : val WuPaper.ClassicalFourthData.Bq 8143 = (275155426117878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8143 = 275155426117878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8143 = (16143:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8143
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_508
