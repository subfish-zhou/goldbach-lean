import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints198
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_198 (j : Fin 16) (hj : 16*198+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*198+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*198+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3168) ≤ val WuPaper.ClassicalFourthData.Bq 3168
    have hp : val WuPaper.ClassicalFourthData.Bq 3168 = (208929912089090:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3168 = 208929912089090 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3168 = (349:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3168
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3169) ≤ val WuPaper.ClassicalFourthData.Bq 3169
    have hp : val WuPaper.ClassicalFourthData.Bq 3169 = (208961165279200:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3169 = 208961165279200 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3169 = (11169:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3169
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3170) ≤ val WuPaper.ClassicalFourthData.Bq 3170
    have hp : val WuPaper.ClassicalFourthData.Bq 3170 = (208992405905690:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3170 = 208992405905690 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3170 = (1117:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3170
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3171) ≤ val WuPaper.ClassicalFourthData.Bq 3171
    have hp : val WuPaper.ClassicalFourthData.Bq 3171 = (209023633973878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3171 = 209023633973878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3171 = (11171:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3171
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3172) ≤ val WuPaper.ClassicalFourthData.Bq 3172
    have hp : val WuPaper.ClassicalFourthData.Bq 3172 = (209054849489079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3172 = 209054849489079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3172 = (2793:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3172
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3173) ≤ val WuPaper.ClassicalFourthData.Bq 3173
    have hp : val WuPaper.ClassicalFourthData.Bq 3173 = (209086052456604:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3173 = 209086052456604 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3173 = (11173:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3173
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3174) ≤ val WuPaper.ClassicalFourthData.Bq 3174
    have hp : val WuPaper.ClassicalFourthData.Bq 3174 = (209117242881762:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3174 = 209117242881762 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3174 = (5587:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3174
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3175) ≤ val WuPaper.ClassicalFourthData.Bq 3175
    have hp : val WuPaper.ClassicalFourthData.Bq 3175 = (209148420769860:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3175 = 209148420769860 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3175 = (447:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3175
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3176) ≤ val WuPaper.ClassicalFourthData.Bq 3176
    have hp : val WuPaper.ClassicalFourthData.Bq 3176 = (209179586126201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3176 = 209179586126201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3176 = (1397:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3176
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3177) ≤ val WuPaper.ClassicalFourthData.Bq 3177
    have hp : val WuPaper.ClassicalFourthData.Bq 3177 = (209210738956087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3177 = 209210738956087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3177 = (11177:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3177
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3178) ≤ val WuPaper.ClassicalFourthData.Bq 3178
    have hp : val WuPaper.ClassicalFourthData.Bq 3178 = (209241879264815:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3178 = 209241879264815 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3178 = (5589:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3178
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3179) ≤ val WuPaper.ClassicalFourthData.Bq 3179
    have hp : val WuPaper.ClassicalFourthData.Bq 3179 = (209273007057682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3179 = 209273007057682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3179 = (11179:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3179
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3180) ≤ val WuPaper.ClassicalFourthData.Bq 3180
    have hp : val WuPaper.ClassicalFourthData.Bq 3180 = (209304122339980:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3180 = 209304122339980 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3180 = (559:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3180
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3181) ≤ val WuPaper.ClassicalFourthData.Bq 3181
    have hp : val WuPaper.ClassicalFourthData.Bq 3181 = (209335225116999:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3181 = 209335225116999 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3181 = (11181:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3181
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3182) ≤ val WuPaper.ClassicalFourthData.Bq 3182
    have hp : val WuPaper.ClassicalFourthData.Bq 3182 = (209366315394027:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3182 = 209366315394027 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3182 = (5591:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3182
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3183) ≤ val WuPaper.ClassicalFourthData.Bq 3183
    have hp : val WuPaper.ClassicalFourthData.Bq 3183 = (209397393176348:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3183 = 209397393176348 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3183 = (11183:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3183
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_198
