import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints458
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_458 (j : Fin 16) (hj : 16*458+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*458+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*458+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7328) ≤ val WuPaper.ClassicalFourthData.Bq 7328
    have hp : val WuPaper.ClassicalFourthData.Bq 7328 = (271655317283937:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7328 = 271655317283937 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7328 = (479:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7328
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7329) ≤ val WuPaper.ClassicalFourthData.Bq 7329
    have hp : val WuPaper.ClassicalFourthData.Bq 7329 = (271660629857664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7329 = 271660629857664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7329 = (15329:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7329
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7330) ≤ val WuPaper.ClassicalFourthData.Bq 7330
    have hp : val WuPaper.ClassicalFourthData.Bq 7330 = (271665939705310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7330 = 271665939705310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7330 = (1533:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7330
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7331) ≤ val WuPaper.ClassicalFourthData.Bq 7331
    have hp : val WuPaper.ClassicalFourthData.Bq 7331 = (271671246827765:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7331 = 271671246827765 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7331 = (15331:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7331
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7332) ≤ val WuPaper.ClassicalFourthData.Bq 7332
    have hp : val WuPaper.ClassicalFourthData.Bq 7332 = (271676551225922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7332 = 271676551225922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7332 = (3833:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7332
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7333) ≤ val WuPaper.ClassicalFourthData.Bq 7333
    have hp : val WuPaper.ClassicalFourthData.Bq 7333 = (271681852900672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7333 = 271681852900672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7333 = (15333:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7333
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7334) ≤ val WuPaper.ClassicalFourthData.Bq 7334
    have hp : val WuPaper.ClassicalFourthData.Bq 7334 = (271687151852907:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7334 = 271687151852907 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7334 = (7667:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7334
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7335) ≤ val WuPaper.ClassicalFourthData.Bq 7335
    have hp : val WuPaper.ClassicalFourthData.Bq 7335 = (271692448083517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7335 = 271692448083517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7335 = (3067:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7335
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7336) ≤ val WuPaper.ClassicalFourthData.Bq 7336
    have hp : val WuPaper.ClassicalFourthData.Bq 7336 = (271697741593394:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7336 = 271697741593394 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7336 = (1917:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7336
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7337) ≤ val WuPaper.ClassicalFourthData.Bq 7337
    have hp : val WuPaper.ClassicalFourthData.Bq 7337 = (271703032383427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7337 = 271703032383427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7337 = (15337:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7337
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7338) ≤ val WuPaper.ClassicalFourthData.Bq 7338
    have hp : val WuPaper.ClassicalFourthData.Bq 7338 = (271708320454507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7338 = 271708320454507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7338 = (7669:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7338
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7339) ≤ val WuPaper.ClassicalFourthData.Bq 7339
    have hp : val WuPaper.ClassicalFourthData.Bq 7339 = (271713605807523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7339 = 271713605807523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7339 = (15339:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7339
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7340) ≤ val WuPaper.ClassicalFourthData.Bq 7340
    have hp : val WuPaper.ClassicalFourthData.Bq 7340 = (271718888443365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7340 = 271718888443365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7340 = (767:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7340
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7341) ≤ val WuPaper.ClassicalFourthData.Bq 7341
    have hp : val WuPaper.ClassicalFourthData.Bq 7341 = (271724168362921:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7341 = 271724168362921 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7341 = (15341:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7341
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7342) ≤ val WuPaper.ClassicalFourthData.Bq 7342
    have hp : val WuPaper.ClassicalFourthData.Bq 7342 = (271729445567080:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7342 = 271729445567080 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7342 = (7671:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7342
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7343) ≤ val WuPaper.ClassicalFourthData.Bq 7343
    have hp : val WuPaper.ClassicalFourthData.Bq 7343 = (271734720056731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7343 = 271734720056731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7343 = (15343:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_458
