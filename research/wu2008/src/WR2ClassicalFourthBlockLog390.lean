import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints390
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_390 (j : Fin 16) (hj : 16*390+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*390+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*390+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6240) ≤ val WuPaper.ClassicalFourthData.Bq 6240
    have hp : val WuPaper.ClassicalFourthData.Bq 6240 = (264046982722333:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6240 = 264046982722333 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6240 = (89:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6240
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6241) ≤ val WuPaper.ClassicalFourthData.Bq 6241
    have hp : val WuPaper.ClassicalFourthData.Bq 6241 = (264055869664615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6241 = 264055869664615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6241 = (14241:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6241
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6242) ≤ val WuPaper.ClassicalFourthData.Bq 6242
    have hp : val WuPaper.ClassicalFourthData.Bq 6242 = (264064752680945:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6242 = 264064752680945 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6242 = (7121:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6242
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6243) ≤ val WuPaper.ClassicalFourthData.Bq 6243
    have hp : val WuPaper.ClassicalFourthData.Bq 6243 = (264073631772672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6243 = 264073631772672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6243 = (14243:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6243
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6244) ≤ val WuPaper.ClassicalFourthData.Bq 6244
    have hp : val WuPaper.ClassicalFourthData.Bq 6244 = (264082506941147:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6244 = 264082506941147 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6244 = (3561:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6244
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6245) ≤ val WuPaper.ClassicalFourthData.Bq 6245
    have hp : val WuPaper.ClassicalFourthData.Bq 6245 = (264091378187717:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6245 = 264091378187717 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6245 = (2849:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6245
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6246) ≤ val WuPaper.ClassicalFourthData.Bq 6246
    have hp : val WuPaper.ClassicalFourthData.Bq 6246 = (264100245513732:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6246 = 264100245513732 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6246 = (7123:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6246
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6247) ≤ val WuPaper.ClassicalFourthData.Bq 6247
    have hp : val WuPaper.ClassicalFourthData.Bq 6247 = (264109108920538:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6247 = 264109108920538 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6247 = (14247:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6247
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6248) ≤ val WuPaper.ClassicalFourthData.Bq 6248
    have hp : val WuPaper.ClassicalFourthData.Bq 6248 = (264117968409483:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6248 = 264117968409483 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6248 = (1781:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6248
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6249) ≤ val WuPaper.ClassicalFourthData.Bq 6249
    have hp : val WuPaper.ClassicalFourthData.Bq 6249 = (264126823981913:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6249 = 264126823981913 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6249 = (14249:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6249
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6250) ≤ val WuPaper.ClassicalFourthData.Bq 6250
    have hp : val WuPaper.ClassicalFourthData.Bq 6250 = (264135675639175:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6250 = 264135675639175 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6250 = (57:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6250
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6251) ≤ val WuPaper.ClassicalFourthData.Bq 6251
    have hp : val WuPaper.ClassicalFourthData.Bq 6251 = (264144523382615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6251 = 264144523382615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6251 = (14251:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6251
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6252) ≤ val WuPaper.ClassicalFourthData.Bq 6252
    have hp : val WuPaper.ClassicalFourthData.Bq 6252 = (264153367213576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6252 = 264153367213576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6252 = (3563:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6252
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6253) ≤ val WuPaper.ClassicalFourthData.Bq 6253
    have hp : val WuPaper.ClassicalFourthData.Bq 6253 = (264162207133403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6253 = 264162207133403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6253 = (14253:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6253
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6254) ≤ val WuPaper.ClassicalFourthData.Bq 6254
    have hp : val WuPaper.ClassicalFourthData.Bq 6254 = (264171043143442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6254 = 264171043143442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6254 = (7127:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6254
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6255) ≤ val WuPaper.ClassicalFourthData.Bq 6255
    have hp : val WuPaper.ClassicalFourthData.Bq 6255 = (264179875245034:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6255 = 264179875245034 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6255 = (2851:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_390
