import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints518
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_518 (j : Fin 16) (hj : 16*518+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*518+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*518+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8288) ≤ val WuPaper.ClassicalFourthData.Bq 8288
    have hp : val WuPaper.ClassicalFourthData.Bq 8288 = (275621025365923:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8288 = 275621025365923 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8288 = (509:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8288
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8289) ≤ val WuPaper.ClassicalFourthData.Bq 8289
    have hp : val WuPaper.ClassicalFourthData.Bq 8289 = (275624087958055:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8289 = 275624087958055 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8289 = (16289:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8289
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8290) ≤ val WuPaper.ClassicalFourthData.Bq 8290
    have hp : val WuPaper.ClassicalFourthData.Bq 8290 = (275627148548234:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8290 = 275627148548234 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8290 = (1629:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8290
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8291) ≤ val WuPaper.ClassicalFourthData.Bq 8291
    have hp : val WuPaper.ClassicalFourthData.Bq 8291 = (275630207137092:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8291 = 275630207137092 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8291 = (16291:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8291
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8292) ≤ val WuPaper.ClassicalFourthData.Bq 8292
    have hp : val WuPaper.ClassicalFourthData.Bq 8292 = (275633263725263:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8292 = 275633263725263 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8292 = (4073:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8292
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8293) ≤ val WuPaper.ClassicalFourthData.Bq 8293
    have hp : val WuPaper.ClassicalFourthData.Bq 8293 = (275636318313379:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8293 = 275636318313379 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8293 = (16293:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8293
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8294) ≤ val WuPaper.ClassicalFourthData.Bq 8294
    have hp : val WuPaper.ClassicalFourthData.Bq 8294 = (275639370902073:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8294 = 275639370902073 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8294 = (8147:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8294
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8295) ≤ val WuPaper.ClassicalFourthData.Bq 8295
    have hp : val WuPaper.ClassicalFourthData.Bq 8295 = (275642421491977:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8295 = 275642421491977 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8295 = (3259:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8295
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8296) ≤ val WuPaper.ClassicalFourthData.Bq 8296
    have hp : val WuPaper.ClassicalFourthData.Bq 8296 = (275645470083724:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8296 = 275645470083724 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8296 = (2037:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8296
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8297) ≤ val WuPaper.ClassicalFourthData.Bq 8297
    have hp : val WuPaper.ClassicalFourthData.Bq 8297 = (275648516677945:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8297 = 275648516677945 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8297 = (16297:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8297
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8298) ≤ val WuPaper.ClassicalFourthData.Bq 8298
    have hp : val WuPaper.ClassicalFourthData.Bq 8298 = (275651561275271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8298 = 275651561275271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8298 = (8149:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8298
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8299) ≤ val WuPaper.ClassicalFourthData.Bq 8299
    have hp : val WuPaper.ClassicalFourthData.Bq 8299 = (275654603876335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8299 = 275654603876335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8299 = (16299:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8299
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8300) ≤ val WuPaper.ClassicalFourthData.Bq 8300
    have hp : val WuPaper.ClassicalFourthData.Bq 8300 = (275657644481768:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8300 = 275657644481768 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8300 = (163:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8300
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8301) ≤ val WuPaper.ClassicalFourthData.Bq 8301
    have hp : val WuPaper.ClassicalFourthData.Bq 8301 = (275660683092201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8301 = 275660683092201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8301 = (16301:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8301
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8302) ≤ val WuPaper.ClassicalFourthData.Bq 8302
    have hp : val WuPaper.ClassicalFourthData.Bq 8302 = (275663719708264:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8302 = 275663719708264 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8302 = (8151:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8302
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8303) ≤ val WuPaper.ClassicalFourthData.Bq 8303
    have hp : val WuPaper.ClassicalFourthData.Bq 8303 = (275666754330588:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8303 = 275666754330588 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8303 = (16303:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_518
