import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints327
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_327 (j : Fin 16) (hj : 16*327+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*327+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*327+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5232) ≤ val WuPaper.ClassicalFourthData.Bq 5232
    have hp : val WuPaper.ClassicalFourthData.Bq 5232 = (252835957873596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5232 = 252835957873596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5232 = (827:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5232
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5233) ≤ val WuPaper.ClassicalFourthData.Bq 5233
    have hp : val WuPaper.ClassicalFourthData.Bq 5233 = (252849591678562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5233 = 252849591678562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5233 = (13233:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5233
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5234) ≤ val WuPaper.ClassicalFourthData.Bq 5234
    have hp : val WuPaper.ClassicalFourthData.Bq 5234 = (252863219877561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5234 = 252863219877561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5234 = (6617:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5234
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5235) ≤ val WuPaper.ClassicalFourthData.Bq 5235
    have hp : val WuPaper.ClassicalFourthData.Bq 5235 = (252876842472630:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5235 = 252876842472630 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5235 = (2647:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5235
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5236) ≤ val WuPaper.ClassicalFourthData.Bq 5236
    have hp : val WuPaper.ClassicalFourthData.Bq 5236 = (252890459465809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5236 = 252890459465809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5236 = (3309:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5236
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5237) ≤ val WuPaper.ClassicalFourthData.Bq 5237
    have hp : val WuPaper.ClassicalFourthData.Bq 5237 = (252904070859133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5237 = 252904070859133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5237 = (13237:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5237
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5238) ≤ val WuPaper.ClassicalFourthData.Bq 5238
    have hp : val WuPaper.ClassicalFourthData.Bq 5238 = (252917676654638:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5238 = 252917676654638 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5238 = (6619:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5238
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5239) ≤ val WuPaper.ClassicalFourthData.Bq 5239
    have hp : val WuPaper.ClassicalFourthData.Bq 5239 = (252931276854361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5239 = 252931276854361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5239 = (13239:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5239
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5240) ≤ val WuPaper.ClassicalFourthData.Bq 5240
    have hp : val WuPaper.ClassicalFourthData.Bq 5240 = (252944871460334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5240 = 252944871460334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5240 = (331:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5240
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5241) ≤ val WuPaper.ClassicalFourthData.Bq 5241
    have hp : val WuPaper.ClassicalFourthData.Bq 5241 = (252958460474591:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5241 = 252958460474591 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5241 = (13241:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5241
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5242) ≤ val WuPaper.ClassicalFourthData.Bq 5242
    have hp : val WuPaper.ClassicalFourthData.Bq 5242 = (252972043899165:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5242 = 252972043899165 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5242 = (6621:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5242
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5243) ≤ val WuPaper.ClassicalFourthData.Bq 5243
    have hp : val WuPaper.ClassicalFourthData.Bq 5243 = (252985621736088:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5243 = 252985621736088 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5243 = (13243:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5243
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5244) ≤ val WuPaper.ClassicalFourthData.Bq 5244
    have hp : val WuPaper.ClassicalFourthData.Bq 5244 = (252999193987390:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5244 = 252999193987390 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5244 = (3311:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5244
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5245) ≤ val WuPaper.ClassicalFourthData.Bq 5245
    have hp : val WuPaper.ClassicalFourthData.Bq 5245 = (253012760655100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5245 = 253012760655100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5245 = (2649:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5245
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5246) ≤ val WuPaper.ClassicalFourthData.Bq 5246
    have hp : val WuPaper.ClassicalFourthData.Bq 5246 = (253026321741249:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5246 = 253026321741249 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5246 = (6623:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5246
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5247) ≤ val WuPaper.ClassicalFourthData.Bq 5247
    have hp : val WuPaper.ClassicalFourthData.Bq 5247 = (253039877247864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5247 = 253039877247864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5247 = (13247:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5247
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_327
