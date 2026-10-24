import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints016
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_016 (j : Fin 16) (hj : 16*16+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*16+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*16+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 256) ≤ val WuPaper.ClassicalFourthData.Bq 256
    have hp : val WuPaper.ClassicalFourthData.Bq 256 = (30055906453224:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 256 = 30055906453224 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 256 = (258:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_256
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 257) ≤ val WuPaper.ClassicalFourthData.Bq 257
    have hp : val WuPaper.ClassicalFourthData.Bq 257 = (30166077619535:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 257 = 30166077619535 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 257 = (8257:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_257
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 258) ≤ val WuPaper.ClassicalFourthData.Bq 258
    have hp : val WuPaper.ClassicalFourthData.Bq 258 = (30276195374860:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 258 = 30276195374860 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 258 = (4129:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_258
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 259) ≤ val WuPaper.ClassicalFourthData.Bq 259
    have hp : val WuPaper.ClassicalFourthData.Bq 259 = (30386259751150:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 259 = 30386259751150 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 259 = (8259:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_259
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 260) ≤ val WuPaper.ClassicalFourthData.Bq 260
    have hp : val WuPaper.ClassicalFourthData.Bq 260 = (30496270780334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 260 = 30496270780334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 260 = (413:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_260
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 261) ≤ val WuPaper.ClassicalFourthData.Bq 261
    have hp : val WuPaper.ClassicalFourthData.Bq 261 = (30606228494316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 261 = 30606228494316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 261 = (8261:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_261
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 262) ≤ val WuPaper.ClassicalFourthData.Bq 262
    have hp : val WuPaper.ClassicalFourthData.Bq 262 = (30716132924975:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 262 = 30716132924975 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 262 = (4131:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_262
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 263) ≤ val WuPaper.ClassicalFourthData.Bq 263
    have hp : val WuPaper.ClassicalFourthData.Bq 263 = (30825984104167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 263 = 30825984104167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 263 = (8263:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_263
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 264) ≤ val WuPaper.ClassicalFourthData.Bq 264
    have hp : val WuPaper.ClassicalFourthData.Bq 264 = (30935782063724:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 264 = 30935782063724 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 264 = (1033:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_264
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 265) ≤ val WuPaper.ClassicalFourthData.Bq 265
    have hp : val WuPaper.ClassicalFourthData.Bq 265 = (31045526835452:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 265 = 31045526835452 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 265 = (1653:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_265
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 266) ≤ val WuPaper.ClassicalFourthData.Bq 266
    have hp : val WuPaper.ClassicalFourthData.Bq 266 = (31155218451134:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 266 = 31155218451134 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 266 = (4133:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_266
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 267) ≤ val WuPaper.ClassicalFourthData.Bq 267
    have hp : val WuPaper.ClassicalFourthData.Bq 267 = (31264856942530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 267 = 31264856942530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 267 = (8267:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_267
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 268) ≤ val WuPaper.ClassicalFourthData.Bq 268
    have hp : val WuPaper.ClassicalFourthData.Bq 268 = (31374442341373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 268 = 31374442341373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 268 = (2067:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_268
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 269) ≤ val WuPaper.ClassicalFourthData.Bq 269
    have hp : val WuPaper.ClassicalFourthData.Bq 269 = (31483974679374:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 269 = 31483974679374 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 269 = (8269:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_269
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 270) ≤ val WuPaper.ClassicalFourthData.Bq 270
    have hp : val WuPaper.ClassicalFourthData.Bq 270 = (31593453988219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 270 = 31593453988219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 270 = (827:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_270
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 271) ≤ val WuPaper.ClassicalFourthData.Bq 271
    have hp : val WuPaper.ClassicalFourthData.Bq 271 = (31702880299572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 271 = 31702880299572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 271 = (8271:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_271
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_016
