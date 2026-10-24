import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints145
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_145 (j : Fin 16) (hj : 16*145+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*145+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*145+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2320) ≤ val WuPaper.ClassicalFourthData.Bq 2320
    have hp : val WuPaper.ClassicalFourthData.Bq 2320 = (177296452340650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2320 = 177296452340650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2320 = (129:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2320
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2321) ≤ val WuPaper.ClassicalFourthData.Bq 2321
    have hp : val WuPaper.ClassicalFourthData.Bq 2321 = (177340591946622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2321 = 177340591946622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2321 = (10321:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2321
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2322) ≤ val WuPaper.ClassicalFourthData.Bq 2322
    have hp : val WuPaper.ClassicalFourthData.Bq 2322 = (177384713301119:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2322 = 177384713301119 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2322 = (5161:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2322
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2323) ≤ val WuPaper.ClassicalFourthData.Bq 2323
    have hp : val WuPaper.ClassicalFourthData.Bq 2323 = (177428816412511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2323 = 177428816412511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2323 = (10323:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2323
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2324) ≤ val WuPaper.ClassicalFourthData.Bq 2324
    have hp : val WuPaper.ClassicalFourthData.Bq 2324 = (177472901289166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2324 = 177472901289166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2324 = (2581:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2324
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2325) ≤ val WuPaper.ClassicalFourthData.Bq 2325
    have hp : val WuPaper.ClassicalFourthData.Bq 2325 = (177516967939446:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2325 = 177516967939446 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2325 = (413:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2325
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2326) ≤ val WuPaper.ClassicalFourthData.Bq 2326
    have hp : val WuPaper.ClassicalFourthData.Bq 2326 = (177561016371709:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2326 = 177561016371709 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2326 = (5163:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2326
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2327) ≤ val WuPaper.ClassicalFourthData.Bq 2327
    have hp : val WuPaper.ClassicalFourthData.Bq 2327 = (177605046594309:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2327 = 177605046594309 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2327 = (10327:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2327
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2328) ≤ val WuPaper.ClassicalFourthData.Bq 2328
    have hp : val WuPaper.ClassicalFourthData.Bq 2328 = (177649058615594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2328 = 177649058615594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2328 = (1291:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2328
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2329) ≤ val WuPaper.ClassicalFourthData.Bq 2329
    have hp : val WuPaper.ClassicalFourthData.Bq 2329 = (177693052443907:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2329 = 177693052443907 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2329 = (10329:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2329
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2330) ≤ val WuPaper.ClassicalFourthData.Bq 2330
    have hp : val WuPaper.ClassicalFourthData.Bq 2330 = (177737028087588:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2330 = 177737028087588 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2330 = (1033:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2330
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2331) ≤ val WuPaper.ClassicalFourthData.Bq 2331
    have hp : val WuPaper.ClassicalFourthData.Bq 2331 = (177780985554971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2331 = 177780985554971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2331 = (10331:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2331
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2332) ≤ val WuPaper.ClassicalFourthData.Bq 2332
    have hp : val WuPaper.ClassicalFourthData.Bq 2332 = (177824924854385:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2332 = 177824924854385 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2332 = (2583:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2332
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2333) ≤ val WuPaper.ClassicalFourthData.Bq 2333
    have hp : val WuPaper.ClassicalFourthData.Bq 2333 = (177868845994156:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2333 = 177868845994156 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2333 = (10333:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2333
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2334) ≤ val WuPaper.ClassicalFourthData.Bq 2334
    have hp : val WuPaper.ClassicalFourthData.Bq 2334 = (177912748982605:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2334 = 177912748982605 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2334 = (5167:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2334
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2335) ≤ val WuPaper.ClassicalFourthData.Bq 2335
    have hp : val WuPaper.ClassicalFourthData.Bq 2335 = (177956633828046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2335 = 177956633828046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2335 = (2067:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2335
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_145
