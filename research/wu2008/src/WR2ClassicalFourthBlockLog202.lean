import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints202
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_202 (j : Fin 16) (hj : 16*202+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*202+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*202+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3232) ≤ val WuPaper.ClassicalFourthData.Bq 3232
    have hp : val WuPaper.ClassicalFourthData.Bq 3232 = (210905007824069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3232 = 210905007824069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3232 = (351:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3232
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3233) ≤ val WuPaper.ClassicalFourthData.Bq 3233
    have hp : val WuPaper.ClassicalFourthData.Bq 3233 = (210935467549988:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3233 = 210935467549988 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3233 = (11233:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3233
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3234) ≤ val WuPaper.ClassicalFourthData.Bq 3234
    have hp : val WuPaper.ClassicalFourthData.Bq 3234 = (210965915047184:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3234 = 210965915047184 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3234 = (5617:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3234
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3235) ≤ val WuPaper.ClassicalFourthData.Bq 3235
    have hp : val WuPaper.ClassicalFourthData.Bq 3235 = (210996350320804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3235 = 210996350320804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3235 = (2247:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3235
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3236) ≤ val WuPaper.ClassicalFourthData.Bq 3236
    have hp : val WuPaper.ClassicalFourthData.Bq 3236 = (211026773375991:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3236 = 211026773375991 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3236 = (2809:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3236
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3237) ≤ val WuPaper.ClassicalFourthData.Bq 3237
    have hp : val WuPaper.ClassicalFourthData.Bq 3237 = (211057184217888:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3237 = 211057184217888 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3237 = (11237:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3237
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3238) ≤ val WuPaper.ClassicalFourthData.Bq 3238
    have hp : val WuPaper.ClassicalFourthData.Bq 3238 = (211087582851632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3238 = 211087582851632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3238 = (5619:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3238
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3239) ≤ val WuPaper.ClassicalFourthData.Bq 3239
    have hp : val WuPaper.ClassicalFourthData.Bq 3239 = (211117969282361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3239 = 211117969282361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3239 = (11239:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3239
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3240) ≤ val WuPaper.ClassicalFourthData.Bq 3240
    have hp : val WuPaper.ClassicalFourthData.Bq 3240 = (211148343515208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3240 = 211148343515208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3240 = (281:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3240
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3241) ≤ val WuPaper.ClassicalFourthData.Bq 3241
    have hp : val WuPaper.ClassicalFourthData.Bq 3241 = (211178705555305:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3241 = 211178705555305 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3241 = (11241:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3241
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3242) ≤ val WuPaper.ClassicalFourthData.Bq 3242
    have hp : val WuPaper.ClassicalFourthData.Bq 3242 = (211209055407778:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3242 = 211209055407778 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3242 = (5621:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3242
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3243) ≤ val WuPaper.ClassicalFourthData.Bq 3243
    have hp : val WuPaper.ClassicalFourthData.Bq 3243 = (211239393077755:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3243 = 211239393077755 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3243 = (11243:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3243
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3244) ≤ val WuPaper.ClassicalFourthData.Bq 3244
    have hp : val WuPaper.ClassicalFourthData.Bq 3244 = (211269718570358:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3244 = 211269718570358 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3244 = (2811:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3244
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3245) ≤ val WuPaper.ClassicalFourthData.Bq 3245
    have hp : val WuPaper.ClassicalFourthData.Bq 3245 = (211300031890709:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3245 = 211300031890709 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3245 = (2249:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3245
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3246) ≤ val WuPaper.ClassicalFourthData.Bq 3246
    have hp : val WuPaper.ClassicalFourthData.Bq 3246 = (211330333043925:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3246 = 211330333043925 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3246 = (5623:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3246
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3247) ≤ val WuPaper.ClassicalFourthData.Bq 3247
    have hp : val WuPaper.ClassicalFourthData.Bq 3247 = (211360622035122:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3247 = 211360622035122 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3247 = (11247:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3247
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_202
