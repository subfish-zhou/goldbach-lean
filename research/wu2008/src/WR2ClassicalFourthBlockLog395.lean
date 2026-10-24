import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints395
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_395 (j : Fin 16) (hj : 16*395+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*395+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*395+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6320) ≤ val WuPaper.ClassicalFourthData.Bq 6320
    have hp : val WuPaper.ClassicalFourthData.Bq 6320 = (264745642160215:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6320 = 264745642160215 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6320 = (179:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6320
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6321) ≤ val WuPaper.ClassicalFourthData.Bq 6321
    have hp : val WuPaper.ClassicalFourthData.Bq 6321 = (264754219248362:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6321 = 264754219248362 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6321 = (14321:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6321
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6322) ≤ val WuPaper.ClassicalFourthData.Bq 6322
    have hp : val WuPaper.ClassicalFourthData.Bq 6322 = (264762792516880:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6322 = 264762792516880 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6322 = (7161:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6322
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6323) ≤ val WuPaper.ClassicalFourthData.Bq 6323
    have hp : val WuPaper.ClassicalFourthData.Bq 6323 = (264771361967076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6323 = 264771361967076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6323 = (14323:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6323
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6324) ≤ val WuPaper.ClassicalFourthData.Bq 6324
    have hp : val WuPaper.ClassicalFourthData.Bq 6324 = (264779927600257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6324 = 264779927600257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6324 = (3581:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6324
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6325) ≤ val WuPaper.ClassicalFourthData.Bq 6325
    have hp : val WuPaper.ClassicalFourthData.Bq 6325 = (264788489417731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6325 = 264788489417731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6325 = (573:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6325
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6326) ≤ val WuPaper.ClassicalFourthData.Bq 6326
    have hp : val WuPaper.ClassicalFourthData.Bq 6326 = (264797047420804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6326 = 264797047420804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6326 = (7163:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6326
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6327) ≤ val WuPaper.ClassicalFourthData.Bq 6327
    have hp : val WuPaper.ClassicalFourthData.Bq 6327 = (264805601610783:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6327 = 264805601610783 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6327 = (14327:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6327
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6328) ≤ val WuPaper.ClassicalFourthData.Bq 6328
    have hp : val WuPaper.ClassicalFourthData.Bq 6328 = (264814151988971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6328 = 264814151988971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6328 = (1791:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6328
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6329) ≤ val WuPaper.ClassicalFourthData.Bq 6329
    have hp : val WuPaper.ClassicalFourthData.Bq 6329 = (264822698556675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6329 = 264822698556675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6329 = (14329:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6329
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6330) ≤ val WuPaper.ClassicalFourthData.Bq 6330
    have hp : val WuPaper.ClassicalFourthData.Bq 6330 = (264831241315199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6330 = 264831241315199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6330 = (1433:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6330
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6331) ≤ val WuPaper.ClassicalFourthData.Bq 6331
    have hp : val WuPaper.ClassicalFourthData.Bq 6331 = (264839780265847:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6331 = 264839780265847 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6331 = (14331:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6331
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6332) ≤ val WuPaper.ClassicalFourthData.Bq 6332
    have hp : val WuPaper.ClassicalFourthData.Bq 6332 = (264848315409921:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6332 = 264848315409921 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6332 = (3583:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6332
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6333) ≤ val WuPaper.ClassicalFourthData.Bq 6333
    have hp : val WuPaper.ClassicalFourthData.Bq 6333 = (264856846748726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6333 = 264856846748726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6333 = (14333:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6333
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6334) ≤ val WuPaper.ClassicalFourthData.Bq 6334
    have hp : val WuPaper.ClassicalFourthData.Bq 6334 = (264865374283563:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6334 = 264865374283563 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6334 = (7167:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6334
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6335) ≤ val WuPaper.ClassicalFourthData.Bq 6335
    have hp : val WuPaper.ClassicalFourthData.Bq 6335 = (264873898015734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6335 = 264873898015734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6335 = (2867:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6335
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_395
