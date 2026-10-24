import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints519
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_519 (j : Fin 16) (hj : 16*519+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*519+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*519+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8304) ≤ val WuPaper.ClassicalFourthData.Bq 8304
    have hp : val WuPaper.ClassicalFourthData.Bq 8304 = (275669786959804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8304 = 275669786959804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8304 = (1019:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8304
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8305) ≤ val WuPaper.ClassicalFourthData.Bq 8305
    have hp : val WuPaper.ClassicalFourthData.Bq 8305 = (275672817596541:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8305 = 275672817596541 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8305 = (3261:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8305
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8306) ≤ val WuPaper.ClassicalFourthData.Bq 8306
    have hp : val WuPaper.ClassicalFourthData.Bq 8306 = (275675846241430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8306 = 275675846241430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8306 = (8153:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8306
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8307) ≤ val WuPaper.ClassicalFourthData.Bq 8307
    have hp : val WuPaper.ClassicalFourthData.Bq 8307 = (275678872895100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8307 = 275678872895100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8307 = (16307:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8307
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8308) ≤ val WuPaper.ClassicalFourthData.Bq 8308
    have hp : val WuPaper.ClassicalFourthData.Bq 8308 = (275681897558181:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8308 = 275681897558181 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8308 = (4077:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8308
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8309) ≤ val WuPaper.ClassicalFourthData.Bq 8309
    have hp : val WuPaper.ClassicalFourthData.Bq 8309 = (275684920231303:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8309 = 275684920231303 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8309 = (16309:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8309
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8310) ≤ val WuPaper.ClassicalFourthData.Bq 8310
    have hp : val WuPaper.ClassicalFourthData.Bq 8310 = (275687940915093:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8310 = 275687940915093 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8310 = (1631:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8310
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8311) ≤ val WuPaper.ClassicalFourthData.Bq 8311
    have hp : val WuPaper.ClassicalFourthData.Bq 8311 = (275690959610181:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8311 = 275690959610181 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8311 = (16311:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8311
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8312) ≤ val WuPaper.ClassicalFourthData.Bq 8312
    have hp : val WuPaper.ClassicalFourthData.Bq 8312 = (275693976317196:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8312 = 275693976317196 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8312 = (2039:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8312
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8313) ≤ val WuPaper.ClassicalFourthData.Bq 8313
    have hp : val WuPaper.ClassicalFourthData.Bq 8313 = (275696991036766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8313 = 275696991036766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8313 = (16313:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8313
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8314) ≤ val WuPaper.ClassicalFourthData.Bq 8314
    have hp : val WuPaper.ClassicalFourthData.Bq 8314 = (275700003769520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8314 = 275700003769520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8314 = (8157:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8314
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8315) ≤ val WuPaper.ClassicalFourthData.Bq 8315
    have hp : val WuPaper.ClassicalFourthData.Bq 8315 = (275703014516084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8315 = 275703014516084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8315 = (3263:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8315
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8316) ≤ val WuPaper.ClassicalFourthData.Bq 8316
    have hp : val WuPaper.ClassicalFourthData.Bq 8316 = (275706023277088:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8316 = 275706023277088 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8316 = (4079:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8316
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8317) ≤ val WuPaper.ClassicalFourthData.Bq 8317
    have hp : val WuPaper.ClassicalFourthData.Bq 8317 = (275709030053158:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8317 = 275709030053158 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8317 = (16317:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8317
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8318) ≤ val WuPaper.ClassicalFourthData.Bq 8318
    have hp : val WuPaper.ClassicalFourthData.Bq 8318 = (275712034844922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8318 = 275712034844922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8318 = (8159:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8318
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8319) ≤ val WuPaper.ClassicalFourthData.Bq 8319
    have hp : val WuPaper.ClassicalFourthData.Bq 8319 = (275715037653007:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8319 = 275715037653007 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8319 = (16319:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_519
