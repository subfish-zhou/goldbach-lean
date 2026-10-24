import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints330
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_330 (j : Fin 16) (hj : 16*330+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*330+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*330+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5280) ≤ val WuPaper.ClassicalFourthData.Bq 5280
    have hp : val WuPaper.ClassicalFourthData.Bq 5280 = (253484092071754:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5280 = 253484092071754 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5280 = (83:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5280
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5281) ≤ val WuPaper.ClassicalFourthData.Bq 5281
    have hp : val WuPaper.ClassicalFourthData.Bq 5281 = (253497459074879:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5281 = 253497459074879 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5281 = (13281:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5281
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5282) ≤ val WuPaper.ClassicalFourthData.Bq 5282
    have hp : val WuPaper.ClassicalFourthData.Bq 5282 = (253510820568919:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5282 = 253510820568919 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5282 = (6641:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5282
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5283) ≤ val WuPaper.ClassicalFourthData.Bq 5283
    have hp : val WuPaper.ClassicalFourthData.Bq 5283 = (253524176555871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5283 = 253524176555871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5283 = (13283:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5283
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5284) ≤ val WuPaper.ClassicalFourthData.Bq 5284
    have hp : val WuPaper.ClassicalFourthData.Bq 5284 = (253537527037731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5284 = 253537527037731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5284 = (3321:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5284
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5285) ≤ val WuPaper.ClassicalFourthData.Bq 5285
    have hp : val WuPaper.ClassicalFourthData.Bq 5285 = (253550872016494:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5285 = 253550872016494 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5285 = (2657:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5285
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5286) ≤ val WuPaper.ClassicalFourthData.Bq 5286
    have hp : val WuPaper.ClassicalFourthData.Bq 5286 = (253564211494157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5286 = 253564211494157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5286 = (6643:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5286
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5287) ≤ val WuPaper.ClassicalFourthData.Bq 5287
    have hp : val WuPaper.ClassicalFourthData.Bq 5287 = (253577545472713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5287 = 253577545472713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5287 = (13287:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5287
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5288) ≤ val WuPaper.ClassicalFourthData.Bq 5288
    have hp : val WuPaper.ClassicalFourthData.Bq 5288 = (253590873954155:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5288 = 253590873954155 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5288 = (1661:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5288
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5289) ≤ val WuPaper.ClassicalFourthData.Bq 5289
    have hp : val WuPaper.ClassicalFourthData.Bq 5289 = (253604196940476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5289 = 253604196940476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5289 = (13289:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5289
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5290) ≤ val WuPaper.ClassicalFourthData.Bq 5290
    have hp : val WuPaper.ClassicalFourthData.Bq 5290 = (253617514433667:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5290 = 253617514433667 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5290 = (1329:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5290
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5291) ≤ val WuPaper.ClassicalFourthData.Bq 5291
    have hp : val WuPaper.ClassicalFourthData.Bq 5291 = (253630826435720:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5291 = 253630826435720 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5291 = (13291:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5291
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5292) ≤ val WuPaper.ClassicalFourthData.Bq 5292
    have hp : val WuPaper.ClassicalFourthData.Bq 5292 = (253644132948623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5292 = 253644132948623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5292 = (3323:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5292
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5293) ≤ val WuPaper.ClassicalFourthData.Bq 5293
    have hp : val WuPaper.ClassicalFourthData.Bq 5293 = (253657433974367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5293 = 253657433974367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5293 = (13293:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5293
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5294) ≤ val WuPaper.ClassicalFourthData.Bq 5294
    have hp : val WuPaper.ClassicalFourthData.Bq 5294 = (253670729514939:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5294 = 253670729514939 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5294 = (6647:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5294
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5295) ≤ val WuPaper.ClassicalFourthData.Bq 5295
    have hp : val WuPaper.ClassicalFourthData.Bq 5295 = (253684019572326:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5295 = 253684019572326 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5295 = (2659:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5295
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_330
