import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints338
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_338 (j : Fin 16) (hj : 16*338+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*338+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*338+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5408) ≤ val WuPaper.ClassicalFourthData.Bq 5408
    have hp : val WuPaper.ClassicalFourthData.Bq 5408 = (255150963614673:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5408 = 255150963614673 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5408 = (419:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5408
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5409) ≤ val WuPaper.ClassicalFourthData.Bq 5409
    have hp : val WuPaper.ClassicalFourthData.Bq 5409 = (255163641406441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5409 = 255163641406441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5409 = (13409:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5409
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5410) ≤ val WuPaper.ClassicalFourthData.Bq 5410
    have hp : val WuPaper.ClassicalFourthData.Bq 5410 = (255176313938077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5410 = 255176313938077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5410 = (1341:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5410
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5411) ≤ val WuPaper.ClassicalFourthData.Bq 5411
    have hp : val WuPaper.ClassicalFourthData.Bq 5411 = (255188981211472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5411 = 255188981211472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5411 = (13411:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5411
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5412) ≤ val WuPaper.ClassicalFourthData.Bq 5412
    have hp : val WuPaper.ClassicalFourthData.Bq 5412 = (255201643228521:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5412 = 255201643228521 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5412 = (3353:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5412
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5413) ≤ val WuPaper.ClassicalFourthData.Bq 5413
    have hp : val WuPaper.ClassicalFourthData.Bq 5413 = (255214299991112:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5413 = 255214299991112 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5413 = (13413:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5413
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5414) ≤ val WuPaper.ClassicalFourthData.Bq 5414
    have hp : val WuPaper.ClassicalFourthData.Bq 5414 = (255226951501137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5414 = 255226951501137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5414 = (6707:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5414
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5415) ≤ val WuPaper.ClassicalFourthData.Bq 5415
    have hp : val WuPaper.ClassicalFourthData.Bq 5415 = (255239597760486:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5415 = 255239597760486 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5415 = (2683:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5415
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5416) ≤ val WuPaper.ClassicalFourthData.Bq 5416
    have hp : val WuPaper.ClassicalFourthData.Bq 5416 = (255252238771046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5416 = 255252238771046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5416 = (1677:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5416
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5417) ≤ val WuPaper.ClassicalFourthData.Bq 5417
    have hp : val WuPaper.ClassicalFourthData.Bq 5417 = (255264874534707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5417 = 255264874534707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5417 = (13417:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5417
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5418) ≤ val WuPaper.ClassicalFourthData.Bq 5418
    have hp : val WuPaper.ClassicalFourthData.Bq 5418 = (255277505053354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5418 = 255277505053354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5418 = (6709:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5418
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5419) ≤ val WuPaper.ClassicalFourthData.Bq 5419
    have hp : val WuPaper.ClassicalFourthData.Bq 5419 = (255290130328875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5419 = 255290130328875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5419 = (13419:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5419
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5420) ≤ val WuPaper.ClassicalFourthData.Bq 5420
    have hp : val WuPaper.ClassicalFourthData.Bq 5420 = (255302750363155:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5420 = 255302750363155 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5420 = (671:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5420
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5421) ≤ val WuPaper.ClassicalFourthData.Bq 5421
    have hp : val WuPaper.ClassicalFourthData.Bq 5421 = (255315365158079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5421 = 255315365158079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5421 = (13421:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5421
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5422) ≤ val WuPaper.ClassicalFourthData.Bq 5422
    have hp : val WuPaper.ClassicalFourthData.Bq 5422 = (255327974715531:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5422 = 255327974715531 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5422 = (6711:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5422
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5423) ≤ val WuPaper.ClassicalFourthData.Bq 5423
    have hp : val WuPaper.ClassicalFourthData.Bq 5423 = (255340579037393:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5423 = 255340579037393 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5423 = (13423:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5423
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_338
