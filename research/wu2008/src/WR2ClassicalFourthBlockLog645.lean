import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints645
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_645 (j : Fin 16) (hj : 16*645+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*645+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*645+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10320) ≤ val WuPaper.ClassicalFourthData.Bq 10320
    have hp : val WuPaper.ClassicalFourthData.Bq 10320 = (278463493573757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10320 = 278463493573757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10320 = (229:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10320
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10321) ≤ val WuPaper.ClassicalFourthData.Bq 10321
    have hp : val WuPaper.ClassicalFourthData.Bq 10321 = (278463540315945:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10321 = 278463540315945 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10321 = (18321:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10321
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10322) ≤ val WuPaper.ClassicalFourthData.Bq 10322
    have hp : val WuPaper.ClassicalFourthData.Bq 10322 = (278463585988543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10322 = 278463585988543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10322 = (9161:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10322
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10323) ≤ val WuPaper.ClassicalFourthData.Bq 10323
    have hp : val WuPaper.ClassicalFourthData.Bq 10323 = (278463630591875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10323 = 278463630591875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10323 = (18323:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10323
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10324) ≤ val WuPaper.ClassicalFourthData.Bq 10324
    have hp : val WuPaper.ClassicalFourthData.Bq 10324 = (278463674126266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10324 = 278463674126266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10324 = (4581:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10324
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10325) ≤ val WuPaper.ClassicalFourthData.Bq 10325
    have hp : val WuPaper.ClassicalFourthData.Bq 10325 = (278463716592038:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10325 = 278463716592038 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10325 = (733:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10325
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10326) ≤ val WuPaper.ClassicalFourthData.Bq 10326
    have hp : val WuPaper.ClassicalFourthData.Bq 10326 = (278463757989515:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10326 = 278463757989515 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10326 = (9163:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10326
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10327) ≤ val WuPaper.ClassicalFourthData.Bq 10327
    have hp : val WuPaper.ClassicalFourthData.Bq 10327 = (278463798319021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10327 = 278463798319021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10327 = (18327:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10327
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10328) ≤ val WuPaper.ClassicalFourthData.Bq 10328
    have hp : val WuPaper.ClassicalFourthData.Bq 10328 = (278463837580878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10328 = 278463837580878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10328 = (2291:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10328
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10329) ≤ val WuPaper.ClassicalFourthData.Bq 10329
    have hp : val WuPaper.ClassicalFourthData.Bq 10329 = (278463875775410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10329 = 278463875775410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10329 = (18329:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10329
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10330) ≤ val WuPaper.ClassicalFourthData.Bq 10330
    have hp : val WuPaper.ClassicalFourthData.Bq 10330 = (278463912902940:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10330 = 278463912902940 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10330 = (1833:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10330
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10331) ≤ val WuPaper.ClassicalFourthData.Bq 10331
    have hp : val WuPaper.ClassicalFourthData.Bq 10331 = (278463948963791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10331 = 278463948963791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10331 = (18331:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10331
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10332) ≤ val WuPaper.ClassicalFourthData.Bq 10332
    have hp : val WuPaper.ClassicalFourthData.Bq 10332 = (278463983958285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10332 = 278463983958285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10332 = (4583:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10332
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10333) ≤ val WuPaper.ClassicalFourthData.Bq 10333
    have hp : val WuPaper.ClassicalFourthData.Bq 10333 = (278464017886746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10333 = 278464017886746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10333 = (18333:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10333
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10334) ≤ val WuPaper.ClassicalFourthData.Bq 10334
    have hp : val WuPaper.ClassicalFourthData.Bq 10334 = (278464050749495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10334 = 278464050749495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10334 = (9167:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10334
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10335) ≤ val WuPaper.ClassicalFourthData.Bq 10335
    have hp : val WuPaper.ClassicalFourthData.Bq 10335 = (278464082546857:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10335 = 278464082546857 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10335 = (3667:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10335
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_645
