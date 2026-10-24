import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints264
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_264 (j : Fin 16) (hj : 16*264+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*264+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*264+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4224) ≤ val WuPaper.ClassicalFourthData.Bq 4224
    have hp : val WuPaper.ClassicalFourthData.Bq 4224 = (235851553531715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4224 = 235851553531715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4224 = (382:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4224
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4225) ≤ val WuPaper.ClassicalFourthData.Bq 4225
    have hp : val WuPaper.ClassicalFourthData.Bq 4225 = (235872044345700:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4225 = 235872044345700 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4225 = (489:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4225
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4226) ≤ val WuPaper.ClassicalFourthData.Bq 4226
    have hp : val WuPaper.ClassicalFourthData.Bq 4226 = (235892526971485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4226 = 235892526971485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4226 = (6113:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4226
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4227) ≤ val WuPaper.ClassicalFourthData.Bq 4227
    have hp : val WuPaper.ClassicalFourthData.Bq 4227 = (235913001412253:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4227 = 235913001412253 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4227 = (12227:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4227
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4228) ≤ val WuPaper.ClassicalFourthData.Bq 4228
    have hp : val WuPaper.ClassicalFourthData.Bq 4228 = (235933467671188:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4228 = 235933467671188 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4228 = (3057:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4228
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4229) ≤ val WuPaper.ClassicalFourthData.Bq 4229
    have hp : val WuPaper.ClassicalFourthData.Bq 4229 = (235953925751472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4229 = 235953925751472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4229 = (12229:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4229
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4230) ≤ val WuPaper.ClassicalFourthData.Bq 4230
    have hp : val WuPaper.ClassicalFourthData.Bq 4230 = (235974375656284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4230 = 235974375656284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4230 = (1223:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4230
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4231) ≤ val WuPaper.ClassicalFourthData.Bq 4231
    have hp : val WuPaper.ClassicalFourthData.Bq 4231 = (235994817388805:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4231 = 235994817388805 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4231 = (12231:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4231
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4232) ≤ val WuPaper.ClassicalFourthData.Bq 4232
    have hp : val WuPaper.ClassicalFourthData.Bq 4232 = (236015250952210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4232 = 236015250952210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4232 = (1529:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4232
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4233) ≤ val WuPaper.ClassicalFourthData.Bq 4233
    have hp : val WuPaper.ClassicalFourthData.Bq 4233 = (236035676349677:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4233 = 236035676349677 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4233 = (12233:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4233
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4234) ≤ val WuPaper.ClassicalFourthData.Bq 4234
    have hp : val WuPaper.ClassicalFourthData.Bq 4234 = (236056093584379:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4234 = 236056093584379 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4234 = (6117:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4234
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4235) ≤ val WuPaper.ClassicalFourthData.Bq 4235
    have hp : val WuPaper.ClassicalFourthData.Bq 4235 = (236076502659490:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4235 = 236076502659490 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4235 = (2447:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4235
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4236) ≤ val WuPaper.ClassicalFourthData.Bq 4236
    have hp : val WuPaper.ClassicalFourthData.Bq 4236 = (236096903578180:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4236 = 236096903578180 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4236 = (3059:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4236
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4237) ≤ val WuPaper.ClassicalFourthData.Bq 4237
    have hp : val WuPaper.ClassicalFourthData.Bq 4237 = (236117296343621:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4237 = 236117296343621 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4237 = (12237:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4237
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4238) ≤ val WuPaper.ClassicalFourthData.Bq 4238
    have hp : val WuPaper.ClassicalFourthData.Bq 4238 = (236137680958980:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4238 = 236137680958980 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4238 = (6119:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4238
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4239) ≤ val WuPaper.ClassicalFourthData.Bq 4239
    have hp : val WuPaper.ClassicalFourthData.Bq 4239 = (236158057427425:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4239 = 236158057427425 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4239 = (12239:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4239
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_264
