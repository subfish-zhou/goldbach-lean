import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints333
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_333 (j : Fin 16) (hj : 16*333+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*333+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*333+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5328) ≤ val WuPaper.ClassicalFourthData.Bq 5328
    have hp : val WuPaper.ClassicalFourthData.Bq 5328 = (254119528357818:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5328 = 254119528357818 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5328 = (833:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5328
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5329) ≤ val WuPaper.ClassicalFourthData.Bq 5329
    have hp : val WuPaper.ClassicalFourthData.Bq 5329 = (254132633163459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5329 = 254132633163459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5329 = (13329:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5329
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5330) ≤ val WuPaper.ClassicalFourthData.Bq 5330
    have hp : val WuPaper.ClassicalFourthData.Bq 5330 = (254145732554948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5330 = 254145732554948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5330 = (1333:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5330
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5331) ≤ val WuPaper.ClassicalFourthData.Bq 5331
    have hp : val WuPaper.ClassicalFourthData.Bq 5331 = (254158826534243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5331 = 254158826534243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5331 = (13331:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5331
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5332) ≤ val WuPaper.ClassicalFourthData.Bq 5332
    have hp : val WuPaper.ClassicalFourthData.Bq 5332 = (254171915103299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5332 = 254171915103299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5332 = (3333:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5332
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5333) ≤ val WuPaper.ClassicalFourthData.Bq 5333
    have hp : val WuPaper.ClassicalFourthData.Bq 5333 = (254184998264073:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5333 = 254184998264073 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5333 = (13333:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5333
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5334) ≤ val WuPaper.ClassicalFourthData.Bq 5334
    have hp : val WuPaper.ClassicalFourthData.Bq 5334 = (254198076018520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5334 = 254198076018520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5334 = (6667:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5334
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5335) ≤ val WuPaper.ClassicalFourthData.Bq 5335
    have hp : val WuPaper.ClassicalFourthData.Bq 5335 = (254211148368594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5335 = 254211148368594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5335 = (2667:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5335
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5336) ≤ val WuPaper.ClassicalFourthData.Bq 5336
    have hp : val WuPaper.ClassicalFourthData.Bq 5336 = (254224215316247:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5336 = 254224215316247 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5336 = (1667:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5336
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5337) ≤ val WuPaper.ClassicalFourthData.Bq 5337
    have hp : val WuPaper.ClassicalFourthData.Bq 5337 = (254237276863433:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5337 = 254237276863433 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5337 = (13337:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5337
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5338) ≤ val WuPaper.ClassicalFourthData.Bq 5338
    have hp : val WuPaper.ClassicalFourthData.Bq 5338 = (254250333012103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5338 = 254250333012103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5338 = (6669:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5338
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5339) ≤ val WuPaper.ClassicalFourthData.Bq 5339
    have hp : val WuPaper.ClassicalFourthData.Bq 5339 = (254263383764208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5339 = 254263383764208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5339 = (13339:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5339
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5340) ≤ val WuPaper.ClassicalFourthData.Bq 5340
    have hp : val WuPaper.ClassicalFourthData.Bq 5340 = (254276429121698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5340 = 254276429121698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5340 = (667:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5340
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5341) ≤ val WuPaper.ClassicalFourthData.Bq 5341
    have hp : val WuPaper.ClassicalFourthData.Bq 5341 = (254289469086523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5341 = 254289469086523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5341 = (13341:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5341
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5342) ≤ val WuPaper.ClassicalFourthData.Bq 5342
    have hp : val WuPaper.ClassicalFourthData.Bq 5342 = (254302503660629:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5342 = 254302503660629 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5342 = (6671:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5342
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5343) ≤ val WuPaper.ClassicalFourthData.Bq 5343
    have hp : val WuPaper.ClassicalFourthData.Bq 5343 = (254315532845966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5343 = 254315532845966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5343 = (13343:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_333
