import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints637
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_637 (j : Fin 16) (hj : 16*637+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*637+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*637+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10192) ≤ val WuPaper.ClassicalFourthData.Bq 10192
    have hp : val WuPaper.ClassicalFourthData.Bq 10192 = (278448563011281:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10192 = 278448563011281 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10192 = (1137:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10192
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10193) ≤ val WuPaper.ClassicalFourthData.Bq 10193
    have hp : val WuPaper.ClassicalFourthData.Bq 10193 = (278448749370725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10193 = 278448749370725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10193 = (18193:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10193
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10194) ≤ val WuPaper.ClassicalFourthData.Bq 10194
    have hp : val WuPaper.ClassicalFourthData.Bq 10194 = (278448934618284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10194 = 278448934618284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10194 = (9097:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10194
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10195) ≤ val WuPaper.ClassicalFourthData.Bq 10195
    have hp : val WuPaper.ClassicalFourthData.Bq 10195 = (278449118754295:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10195 = 278449118754295 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10195 = (3639:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10195
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10196) ≤ val WuPaper.ClassicalFourthData.Bq 10196
    have hp : val WuPaper.ClassicalFourthData.Bq 10196 = (278449301779097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10196 = 278449301779097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10196 = (4549:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10196
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10197) ≤ val WuPaper.ClassicalFourthData.Bq 10197
    have hp : val WuPaper.ClassicalFourthData.Bq 10197 = (278449483693025:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10197 = 278449483693025 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10197 = (18197:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10197
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10198) ≤ val WuPaper.ClassicalFourthData.Bq 10198
    have hp : val WuPaper.ClassicalFourthData.Bq 10198 = (278449664496417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10198 = 278449664496417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10198 = (9099:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10198
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10199) ≤ val WuPaper.ClassicalFourthData.Bq 10199
    have hp : val WuPaper.ClassicalFourthData.Bq 10199 = (278449844189608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10199 = 278449844189608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10199 = (18199:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10199
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10200) ≤ val WuPaper.ClassicalFourthData.Bq 10200
    have hp : val WuPaper.ClassicalFourthData.Bq 10200 = (278450022772937:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10200 = 278450022772937 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10200 = (91:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10200
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10201) ≤ val WuPaper.ClassicalFourthData.Bq 10201
    have hp : val WuPaper.ClassicalFourthData.Bq 10201 = (278450200246738:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10201 = 278450200246738 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10201 = (18201:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10201
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10202) ≤ val WuPaper.ClassicalFourthData.Bq 10202
    have hp : val WuPaper.ClassicalFourthData.Bq 10202 = (278450376611349:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10202 = 278450376611349 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10202 = (9101:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10202
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10203) ≤ val WuPaper.ClassicalFourthData.Bq 10203
    have hp : val WuPaper.ClassicalFourthData.Bq 10203 = (278450551867105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10203 = 278450551867105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10203 = (18203:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10203
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10204) ≤ val WuPaper.ClassicalFourthData.Bq 10204
    have hp : val WuPaper.ClassicalFourthData.Bq 10204 = (278450726014344:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10204 = 278450726014344 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10204 = (4551:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10204
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10205) ≤ val WuPaper.ClassicalFourthData.Bq 10205
    have hp : val WuPaper.ClassicalFourthData.Bq 10205 = (278450899053400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10205 = 278450899053400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10205 = (3641:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10205
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10206) ≤ val WuPaper.ClassicalFourthData.Bq 10206
    have hp : val WuPaper.ClassicalFourthData.Bq 10206 = (278451070984610:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10206 = 278451070984610 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10206 = (9103:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10206
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10207) ≤ val WuPaper.ClassicalFourthData.Bq 10207
    have hp : val WuPaper.ClassicalFourthData.Bq 10207 = (278451241808309:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10207 = 278451241808309 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10207 = (18207:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10207
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_637
