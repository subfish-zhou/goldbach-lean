import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints455
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_455 (j : Fin 16) (hj : 16*455+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*455+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*455+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7280) ≤ val WuPaper.ClassicalFourthData.Bq 7280
    have hp : val WuPaper.ClassicalFourthData.Bq 7280 = (271397090301187:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7280 = 271397090301187 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7280 = (191:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7280
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7281) ≤ val WuPaper.ClassicalFourthData.Bq 7281
    have hp : val WuPaper.ClassicalFourthData.Bq 7281 = (271402534782646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7281 = 271402534782646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7281 = (15281:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7281
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7282) ≤ val WuPaper.ClassicalFourthData.Bq 7282
    have hp : val WuPaper.ClassicalFourthData.Bq 7282 = (271407976494806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7282 = 271407976494806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7282 = (7641:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7282
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7283) ≤ val WuPaper.ClassicalFourthData.Bq 7283
    have hp : val WuPaper.ClassicalFourthData.Bq 7283 = (271413415438574:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7283 = 271413415438574 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7283 = (15283:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7283
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7284) ≤ val WuPaper.ClassicalFourthData.Bq 7284
    have hp : val WuPaper.ClassicalFourthData.Bq 7284 = (271418851614859:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7284 = 271418851614859 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7284 = (3821:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7284
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7285) ≤ val WuPaper.ClassicalFourthData.Bq 7285
    have hp : val WuPaper.ClassicalFourthData.Bq 7285 = (271424285024567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7285 = 271424285024567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7285 = (3057:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7285
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7286) ≤ val WuPaper.ClassicalFourthData.Bq 7286
    have hp : val WuPaper.ClassicalFourthData.Bq 7286 = (271429715668606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7286 = 271429715668606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7286 = (7643:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7286
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7287) ≤ val WuPaper.ClassicalFourthData.Bq 7287
    have hp : val WuPaper.ClassicalFourthData.Bq 7287 = (271435143547882:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7287 = 271435143547882 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7287 = (15287:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7287
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7288) ≤ val WuPaper.ClassicalFourthData.Bq 7288
    have hp : val WuPaper.ClassicalFourthData.Bq 7288 = (271440568663303:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7288 = 271440568663303 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7288 = (1911:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7288
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7289) ≤ val WuPaper.ClassicalFourthData.Bq 7289
    have hp : val WuPaper.ClassicalFourthData.Bq 7289 = (271445991015774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7289 = 271445991015774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7289 = (15289:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7289
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7290) ≤ val WuPaper.ClassicalFourthData.Bq 7290
    have hp : val WuPaper.ClassicalFourthData.Bq 7290 = (271451410606201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7290 = 271451410606201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7290 = (1529:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7290
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7291) ≤ val WuPaper.ClassicalFourthData.Bq 7291
    have hp : val WuPaper.ClassicalFourthData.Bq 7291 = (271456827435490:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7291 = 271456827435490 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7291 = (15291:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7291
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7292) ≤ val WuPaper.ClassicalFourthData.Bq 7292
    have hp : val WuPaper.ClassicalFourthData.Bq 7292 = (271462241504546:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7292 = 271462241504546 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7292 = (3823:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7292
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7293) ≤ val WuPaper.ClassicalFourthData.Bq 7293
    have hp : val WuPaper.ClassicalFourthData.Bq 7293 = (271467652814273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7293 = 271467652814273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7293 = (15293:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7293
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7294) ≤ val WuPaper.ClassicalFourthData.Bq 7294
    have hp : val WuPaper.ClassicalFourthData.Bq 7294 = (271473061365577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7294 = 271473061365577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7294 = (7647:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7294
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7295) ≤ val WuPaper.ClassicalFourthData.Bq 7295
    have hp : val WuPaper.ClassicalFourthData.Bq 7295 = (271478467159361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7295 = 271478467159361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7295 = (3059:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7295
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_455
