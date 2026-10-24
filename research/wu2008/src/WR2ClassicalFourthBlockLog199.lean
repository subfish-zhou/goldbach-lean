import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints199
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_199 (j : Fin 16) (hj : 16*199+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*199+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*199+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3184) ≤ val WuPaper.ClassicalFourthData.Bq 3184
    have hp : val WuPaper.ClassicalFourthData.Bq 3184 = (209428458469245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3184 = 209428458469245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3184 = (699:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3184
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3185) ≤ val WuPaper.ClassicalFourthData.Bq 3185
    have hp : val WuPaper.ClassicalFourthData.Bq 3185 = (209459511277997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3185 = 209459511277997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3185 = (2237:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3185
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3186) ≤ val WuPaper.ClassicalFourthData.Bq 3186
    have hp : val WuPaper.ClassicalFourthData.Bq 3186 = (209490551607880:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3186 = 209490551607880 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3186 = (5593:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3186
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3187) ≤ val WuPaper.ClassicalFourthData.Bq 3187
    have hp : val WuPaper.ClassicalFourthData.Bq 3187 = (209521579464170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3187 = 209521579464170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3187 = (11187:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3187
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3188) ≤ val WuPaper.ClassicalFourthData.Bq 3188
    have hp : val WuPaper.ClassicalFourthData.Bq 3188 = (209552594852136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3188 = 209552594852136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3188 = (2797:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3188
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3189) ≤ val WuPaper.ClassicalFourthData.Bq 3189
    have hp : val WuPaper.ClassicalFourthData.Bq 3189 = (209583597777047:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3189 = 209583597777047 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3189 = (11189:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3189
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3190) ≤ val WuPaper.ClassicalFourthData.Bq 3190
    have hp : val WuPaper.ClassicalFourthData.Bq 3190 = (209614588244170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3190 = 209614588244170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3190 = (1119:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3190
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3191) ≤ val WuPaper.ClassicalFourthData.Bq 3191
    have hp : val WuPaper.ClassicalFourthData.Bq 3191 = (209645566258768:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3191 = 209645566258768 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3191 = (11191:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3191
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3192) ≤ val WuPaper.ClassicalFourthData.Bq 3192
    have hp : val WuPaper.ClassicalFourthData.Bq 3192 = (209676531826101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3192 = 209676531826101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3192 = (1399:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3192
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3193) ≤ val WuPaper.ClassicalFourthData.Bq 3193
    have hp : val WuPaper.ClassicalFourthData.Bq 3193 = (209707484951427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3193 = 209707484951427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3193 = (11193:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3193
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3194) ≤ val WuPaper.ClassicalFourthData.Bq 3194
    have hp : val WuPaper.ClassicalFourthData.Bq 3194 = (209738425640001:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3194 = 209738425640001 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3194 = (5597:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3194
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3195) ≤ val WuPaper.ClassicalFourthData.Bq 3195
    have hp : val WuPaper.ClassicalFourthData.Bq 3195 = (209769353897076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3195 = 209769353897076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3195 = (2239:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3195
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3196) ≤ val WuPaper.ClassicalFourthData.Bq 3196
    have hp : val WuPaper.ClassicalFourthData.Bq 3196 = (209800269727902:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3196 = 209800269727902 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3196 = (2799:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3196
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3197) ≤ val WuPaper.ClassicalFourthData.Bq 3197
    have hp : val WuPaper.ClassicalFourthData.Bq 3197 = (209831173137725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3197 = 209831173137725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3197 = (11197:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3197
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3198) ≤ val WuPaper.ClassicalFourthData.Bq 3198
    have hp : val WuPaper.ClassicalFourthData.Bq 3198 = (209862064131791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3198 = 209862064131791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3198 = (5599:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3198
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3199) ≤ val WuPaper.ClassicalFourthData.Bq 3199
    have hp : val WuPaper.ClassicalFourthData.Bq 3199 = (209892942715341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3199 = 209892942715341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3199 = (11199:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3199
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_199
