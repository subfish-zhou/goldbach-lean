import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints514
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_514 (j : Fin 16) (hj : 16*514+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*514+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*514+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8224) ≤ val WuPaper.ClassicalFourthData.Bq 8224
    have hp : val WuPaper.ClassicalFourthData.Bq 8224 = (275420826259450:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8224 = 275420826259450 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8224 = (507:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8224
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8225) ≤ val WuPaper.ClassicalFourthData.Bq 8225
    have hp : val WuPaper.ClassicalFourthData.Bq 8225 = (275424018303878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8225 = 275424018303878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8225 = (649:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8225
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8226) ≤ val WuPaper.ClassicalFourthData.Bq 8226
    have hp : val WuPaper.ClassicalFourthData.Bq 8226 = (275427208305365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8226 = 275427208305365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8226 = (8113:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8226
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8227) ≤ val WuPaper.ClassicalFourthData.Bq 8227
    have hp : val WuPaper.ClassicalFourthData.Bq 8227 = (275430396264557:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8227 = 275430396264557 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8227 = (16227:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8227
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8228) ≤ val WuPaper.ClassicalFourthData.Bq 8228
    have hp : val WuPaper.ClassicalFourthData.Bq 8228 = (275433582182101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8228 = 275433582182101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8228 = (4057:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8228
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8229) ≤ val WuPaper.ClassicalFourthData.Bq 8229
    have hp : val WuPaper.ClassicalFourthData.Bq 8229 = (275436766058645:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8229 = 275436766058645 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8229 = (16229:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8229
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8230) ≤ val WuPaper.ClassicalFourthData.Bq 8230
    have hp : val WuPaper.ClassicalFourthData.Bq 8230 = (275439947894835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8230 = 275439947894835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8230 = (1623:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8230
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8231) ≤ val WuPaper.ClassicalFourthData.Bq 8231
    have hp : val WuPaper.ClassicalFourthData.Bq 8231 = (275443127691318:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8231 = 275443127691318 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8231 = (16231:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8231
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8232) ≤ val WuPaper.ClassicalFourthData.Bq 8232
    have hp : val WuPaper.ClassicalFourthData.Bq 8232 = (275446305448741:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8232 = 275446305448741 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8232 = (2029:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8232
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8233) ≤ val WuPaper.ClassicalFourthData.Bq 8233
    have hp : val WuPaper.ClassicalFourthData.Bq 8233 = (275449481167749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8233 = 275449481167749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8233 = (16233:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8233
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8234) ≤ val WuPaper.ClassicalFourthData.Bq 8234
    have hp : val WuPaper.ClassicalFourthData.Bq 8234 = (275452654848988:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8234 = 275452654848988 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8234 = (8117:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8234
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8235) ≤ val WuPaper.ClassicalFourthData.Bq 8235
    have hp : val WuPaper.ClassicalFourthData.Bq 8235 = (275455826493105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8235 = 275455826493105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8235 = (3247:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8235
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8236) ≤ val WuPaper.ClassicalFourthData.Bq 8236
    have hp : val WuPaper.ClassicalFourthData.Bq 8236 = (275458996100744:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8236 = 275458996100744 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8236 = (4059:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8236
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8237) ≤ val WuPaper.ClassicalFourthData.Bq 8237
    have hp : val WuPaper.ClassicalFourthData.Bq 8237 = (275462163672551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8237 = 275462163672551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8237 = (16237:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8237
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8238) ≤ val WuPaper.ClassicalFourthData.Bq 8238
    have hp : val WuPaper.ClassicalFourthData.Bq 8238 = (275465329209171:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8238 = 275465329209171 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8238 = (8119:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8238
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8239) ≤ val WuPaper.ClassicalFourthData.Bq 8239
    have hp : val WuPaper.ClassicalFourthData.Bq 8239 = (275468492711248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8239 = 275468492711248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8239 = (16239:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8239
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_514
