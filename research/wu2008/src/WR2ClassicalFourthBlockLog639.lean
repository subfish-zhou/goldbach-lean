import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints639
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_639 (j : Fin 16) (hj : 16*639+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*639+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*639+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10224) ≤ val WuPaper.ClassicalFourthData.Bq 10224
    have hp : val WuPaper.ClassicalFourthData.Bq 10224 = (278453976687005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10224 = 278453976687005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10224 = (1139:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10224
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10225) ≤ val WuPaper.ClassicalFourthData.Bq 10225
    have hp : val WuPaper.ClassicalFourthData.Bq 10225 = (278454127632822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10225 = 278454127632822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10225 = (729:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10225
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10226) ≤ val WuPaper.ClassicalFourthData.Bq 10226
    have hp : val WuPaper.ClassicalFourthData.Bq 10226 = (278454277477489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10226 = 278454277477489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10226 = (9113:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10226
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10227) ≤ val WuPaper.ClassicalFourthData.Bq 10227
    have hp : val WuPaper.ClassicalFourthData.Bq 10227 = (278454426221339:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10227 = 278454426221339 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10227 = (18227:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10227
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10228) ≤ val WuPaper.ClassicalFourthData.Bq 10228
    have hp : val WuPaper.ClassicalFourthData.Bq 10228 = (278454573864707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10228 = 278454573864707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10228 = (4557:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10228
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10229) ≤ val WuPaper.ClassicalFourthData.Bq 10229
    have hp : val WuPaper.ClassicalFourthData.Bq 10229 = (278454720407926:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10229 = 278454720407926 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10229 = (18229:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10229
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10230) ≤ val WuPaper.ClassicalFourthData.Bq 10230
    have hp : val WuPaper.ClassicalFourthData.Bq 10230 = (278454865851329:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10230 = 278454865851329 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10230 = (1823:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10230
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10231) ≤ val WuPaper.ClassicalFourthData.Bq 10231
    have hp : val WuPaper.ClassicalFourthData.Bq 10231 = (278455010195250:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10231 = 278455010195250 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10231 = (18231:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10231
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10232) ≤ val WuPaper.ClassicalFourthData.Bq 10232
    have hp : val WuPaper.ClassicalFourthData.Bq 10232 = (278455153440021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10232 = 278455153440021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10232 = (2279:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10232
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10233) ≤ val WuPaper.ClassicalFourthData.Bq 10233
    have hp : val WuPaper.ClassicalFourthData.Bq 10233 = (278455295585976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10233 = 278455295585976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10233 = (18233:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10233
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10234) ≤ val WuPaper.ClassicalFourthData.Bq 10234
    have hp : val WuPaper.ClassicalFourthData.Bq 10234 = (278455436633448:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10234 = 278455436633448 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10234 = (9117:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10234
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10235) ≤ val WuPaper.ClassicalFourthData.Bq 10235
    have hp : val WuPaper.ClassicalFourthData.Bq 10235 = (278455576582769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10235 = 278455576582769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10235 = (3647:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10235
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10236) ≤ val WuPaper.ClassicalFourthData.Bq 10236
    have hp : val WuPaper.ClassicalFourthData.Bq 10236 = (278455715434273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10236 = 278455715434273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10236 = (4559:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10236
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10237) ≤ val WuPaper.ClassicalFourthData.Bq 10237
    have hp : val WuPaper.ClassicalFourthData.Bq 10237 = (278455853188292:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10237 = 278455853188292 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10237 = (18237:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10237
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10238) ≤ val WuPaper.ClassicalFourthData.Bq 10238
    have hp : val WuPaper.ClassicalFourthData.Bq 10238 = (278455989845159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10238 = 278455989845159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10238 = (9119:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10238
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10239) ≤ val WuPaper.ClassicalFourthData.Bq 10239
    have hp : val WuPaper.ClassicalFourthData.Bq 10239 = (278456125405205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10239 = 278456125405205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10239 = (18239:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10239
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_639
