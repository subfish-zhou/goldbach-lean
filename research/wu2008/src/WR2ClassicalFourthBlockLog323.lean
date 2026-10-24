import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints323
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_323 (j : Fin 16) (hj : 16*323+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*323+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*323+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5168) ≤ val WuPaper.ClassicalFourthData.Bq 5168
    have hp : val WuPaper.ClassicalFourthData.Bq 5168 = (251951639991645:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5168 = 251951639991645 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5168 = (823:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5168
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5169) ≤ val WuPaper.ClassicalFourthData.Bq 5169
    have hp : val WuPaper.ClassicalFourthData.Bq 5169 = (251965636858646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5169 = 251965636858646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5169 = (13169:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5169
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5170) ≤ val WuPaper.ClassicalFourthData.Bq 5170
    have hp : val WuPaper.ClassicalFourthData.Bq 5170 = (251979627987391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5170 = 251979627987391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5170 = (1317:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5170
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5171) ≤ val WuPaper.ClassicalFourthData.Bq 5171
    have hp : val WuPaper.ClassicalFourthData.Bq 5171 = (251993613379977:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5171 = 251993613379977 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5171 = (13171:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5171
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5172) ≤ val WuPaper.ClassicalFourthData.Bq 5172
    have hp : val WuPaper.ClassicalFourthData.Bq 5172 = (252007593038497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5172 = 252007593038497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5172 = (3293:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5172
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5173) ≤ val WuPaper.ClassicalFourthData.Bq 5173
    have hp : val WuPaper.ClassicalFourthData.Bq 5173 = (252021566965044:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5173 = 252021566965044 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5173 = (13173:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5173
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5174) ≤ val WuPaper.ClassicalFourthData.Bq 5174
    have hp : val WuPaper.ClassicalFourthData.Bq 5174 = (252035535161710:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5174 = 252035535161710 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5174 = (6587:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5174
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5175) ≤ val WuPaper.ClassicalFourthData.Bq 5175
    have hp : val WuPaper.ClassicalFourthData.Bq 5175 = (252049497630587:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5175 = 252049497630587 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5175 = (527:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5175
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5176) ≤ val WuPaper.ClassicalFourthData.Bq 5176
    have hp : val WuPaper.ClassicalFourthData.Bq 5176 = (252063454373765:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5176 = 252063454373765 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5176 = (1647:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5176
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5177) ≤ val WuPaper.ClassicalFourthData.Bq 5177
    have hp : val WuPaper.ClassicalFourthData.Bq 5177 = (252077405393333:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5177 = 252077405393333 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5177 = (13177:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5177
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5178) ≤ val WuPaper.ClassicalFourthData.Bq 5178
    have hp : val WuPaper.ClassicalFourthData.Bq 5178 = (252091350691381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5178 = 252091350691381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5178 = (6589:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5178
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5179) ≤ val WuPaper.ClassicalFourthData.Bq 5179
    have hp : val WuPaper.ClassicalFourthData.Bq 5179 = (252105290269995:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5179 = 252105290269995 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5179 = (13179:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5179
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5180) ≤ val WuPaper.ClassicalFourthData.Bq 5180
    have hp : val WuPaper.ClassicalFourthData.Bq 5180 = (252119224131263:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5180 = 252119224131263 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5180 = (659:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5180
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5181) ≤ val WuPaper.ClassicalFourthData.Bq 5181
    have hp : val WuPaper.ClassicalFourthData.Bq 5181 = (252133152277270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5181 = 252133152277270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5181 = (13181:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5181
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5182) ≤ val WuPaper.ClassicalFourthData.Bq 5182
    have hp : val WuPaper.ClassicalFourthData.Bq 5182 = (252147074710102:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5182 = 252147074710102 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5182 = (6591:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5182
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5183) ≤ val WuPaper.ClassicalFourthData.Bq 5183
    have hp : val WuPaper.ClassicalFourthData.Bq 5183 = (252160991431843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5183 = 252160991431843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5183 = (13183:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5183
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_323
