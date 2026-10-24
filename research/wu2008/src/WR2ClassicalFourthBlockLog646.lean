import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints646
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_646 (j : Fin 16) (hj : 16*646+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*646+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*646+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10336) ≤ val WuPaper.ClassicalFourthData.Bq 10336
    have hp : val WuPaper.ClassicalFourthData.Bq 10336 = (278464113279152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10336 = 278464113279152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10336 = (573:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10336
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10337) ≤ val WuPaper.ClassicalFourthData.Bq 10337
    have hp : val WuPaper.ClassicalFourthData.Bq 10337 = (278464142946704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10337 = 278464142946704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10337 = (18337:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10337
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10338) ≤ val WuPaper.ClassicalFourthData.Bq 10338
    have hp : val WuPaper.ClassicalFourthData.Bq 10338 = (278464171549834:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10338 = 278464171549834 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10338 = (9169:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10338
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10339) ≤ val WuPaper.ClassicalFourthData.Bq 10339
    have hp : val WuPaper.ClassicalFourthData.Bq 10339 = (278464199088865:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10339 = 278464199088865 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10339 = (18339:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10339
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10340) ≤ val WuPaper.ClassicalFourthData.Bq 10340
    have hp : val WuPaper.ClassicalFourthData.Bq 10340 = (278464225564118:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10340 = 278464225564118 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10340 = (917:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10340
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10341) ≤ val WuPaper.ClassicalFourthData.Bq 10341
    have hp : val WuPaper.ClassicalFourthData.Bq 10341 = (278464250975917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10341 = 278464250975917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10341 = (18341:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10341
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10342) ≤ val WuPaper.ClassicalFourthData.Bq 10342
    have hp : val WuPaper.ClassicalFourthData.Bq 10342 = (278464275324582:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10342 = 278464275324582 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10342 = (9171:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10342
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10343) ≤ val WuPaper.ClassicalFourthData.Bq 10343
    have hp : val WuPaper.ClassicalFourthData.Bq 10343 = (278464298610435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10343 = 278464298610435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10343 = (18343:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10343
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10344) ≤ val WuPaper.ClassicalFourthData.Bq 10344
    have hp : val WuPaper.ClassicalFourthData.Bq 10344 = (278464320833798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10344 = 278464320833798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10344 = (2293:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10344
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10345) ≤ val WuPaper.ClassicalFourthData.Bq 10345
    have hp : val WuPaper.ClassicalFourthData.Bq 10345 = (278464341994992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10345 = 278464341994992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10345 = (3669:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10345
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10346) ≤ val WuPaper.ClassicalFourthData.Bq 10346
    have hp : val WuPaper.ClassicalFourthData.Bq 10346 = (278464362094339:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10346 = 278464362094339 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10346 = (9173:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10346
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10347) ≤ val WuPaper.ClassicalFourthData.Bq 10347
    have hp : val WuPaper.ClassicalFourthData.Bq 10347 = (278464381132161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10347 = 278464381132161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10347 = (18347:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10347
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10348) ≤ val WuPaper.ClassicalFourthData.Bq 10348
    have hp : val WuPaper.ClassicalFourthData.Bq 10348 = (278464399108777:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10348 = 278464399108777 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10348 = (4587:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10348
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10349) ≤ val WuPaper.ClassicalFourthData.Bq 10349
    have hp : val WuPaper.ClassicalFourthData.Bq 10349 = (278464416024511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10349 = 278464416024511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10349 = (18349:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10349
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10350) ≤ val WuPaper.ClassicalFourthData.Bq 10350
    have hp : val WuPaper.ClassicalFourthData.Bq 10350 = (278464431879681:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10350 = 278464431879681 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10350 = (367:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10350
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10351) ≤ val WuPaper.ClassicalFourthData.Bq 10351
    have hp : val WuPaper.ClassicalFourthData.Bq 10351 = (278464446674611:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10351 = 278464446674611 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10351 = (18351:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10351
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_646
