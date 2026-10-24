import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints642
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_642 (j : Fin 16) (hj : 16*642+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*642+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*642+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10272) ≤ val WuPaper.ClassicalFourthData.Bq 10272
    have hp : val WuPaper.ClassicalFourthData.Bq 10272 = (278459985740409:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10272 = 278459985740409 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10272 = (571:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10272
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10273) ≤ val WuPaper.ClassicalFourthData.Bq 10273
    have hp : val WuPaper.ClassicalFourthData.Bq 10273 = (278460084205633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10273 = 278460084205633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10273 = (18273:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10273
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10274) ≤ val WuPaper.ClassicalFourthData.Bq 10274
    have hp : val WuPaper.ClassicalFourthData.Bq 10274 = (278460181585607:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10274 = 278460181585607 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10274 = (9137:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10274
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10275) ≤ val WuPaper.ClassicalFourthData.Bq 10275
    have hp : val WuPaper.ClassicalFourthData.Bq 10275 = (278460277880659:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10275 = 278460277880659 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10275 = (731:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10275
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10276) ≤ val WuPaper.ClassicalFourthData.Bq 10276
    have hp : val WuPaper.ClassicalFourthData.Bq 10276 = (278460373091118:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10276 = 278460373091118 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10276 = (4569:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10276
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10277) ≤ val WuPaper.ClassicalFourthData.Bq 10277
    have hp : val WuPaper.ClassicalFourthData.Bq 10277 = (278460467217313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10277 = 278460467217313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10277 = (18277:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10277
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10278) ≤ val WuPaper.ClassicalFourthData.Bq 10278
    have hp : val WuPaper.ClassicalFourthData.Bq 10278 = (278460560259571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10278 = 278460560259571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10278 = (9139:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10278
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10279) ≤ val WuPaper.ClassicalFourthData.Bq 10279
    have hp : val WuPaper.ClassicalFourthData.Bq 10279 = (278460652218222:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10279 = 278460652218222 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10279 = (18279:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10279
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10280) ≤ val WuPaper.ClassicalFourthData.Bq 10280
    have hp : val WuPaper.ClassicalFourthData.Bq 10280 = (278460743093593:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10280 = 278460743093593 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10280 = (457:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10280
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10281) ≤ val WuPaper.ClassicalFourthData.Bq 10281
    have hp : val WuPaper.ClassicalFourthData.Bq 10281 = (278460832886012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10281 = 278460832886012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10281 = (18281:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10281
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10282) ≤ val WuPaper.ClassicalFourthData.Bq 10282
    have hp : val WuPaper.ClassicalFourthData.Bq 10282 = (278460921595808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10282 = 278460921595808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10282 = (9141:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10282
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10283) ≤ val WuPaper.ClassicalFourthData.Bq 10283
    have hp : val WuPaper.ClassicalFourthData.Bq 10283 = (278461009223307:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10283 = 278461009223307 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10283 = (18283:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10283
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10284) ≤ val WuPaper.ClassicalFourthData.Bq 10284
    have hp : val WuPaper.ClassicalFourthData.Bq 10284 = (278461095768839:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10284 = 278461095768839 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10284 = (4571:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10284
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10285) ≤ val WuPaper.ClassicalFourthData.Bq 10285
    have hp : val WuPaper.ClassicalFourthData.Bq 10285 = (278461181232730:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10285 = 278461181232730 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10285 = (3657:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10285
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10286) ≤ val WuPaper.ClassicalFourthData.Bq 10286
    have hp : val WuPaper.ClassicalFourthData.Bq 10286 = (278461265615309:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10286 = 278461265615309 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10286 = (9143:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10286
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10287) ≤ val WuPaper.ClassicalFourthData.Bq 10287
    have hp : val WuPaper.ClassicalFourthData.Bq 10287 = (278461348916902:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10287 = 278461348916902 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10287 = (18287:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10287
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_642
