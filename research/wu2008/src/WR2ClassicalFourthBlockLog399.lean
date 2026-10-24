import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints399
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_399 (j : Fin 16) (hj : 16*399+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*399+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*399+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6384) ≤ val WuPaper.ClassicalFourthData.Bq 6384
    have hp : val WuPaper.ClassicalFourthData.Bq 6384 = (265286929600082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6384 = 265286929600082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6384 = (899:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6384
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6385) ≤ val WuPaper.ClassicalFourthData.Bq 6385
    have hp : val WuPaper.ClassicalFourthData.Bq 6385 = (265295264847615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6385 = 265295264847615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6385 = (2877:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6385
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6386) ≤ val WuPaper.ClassicalFourthData.Bq 6386
    have hp : val WuPaper.ClassicalFourthData.Bq 6386 = (265303596358206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6386 = 265303596358206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6386 = (7193:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6386
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6387) ≤ val WuPaper.ClassicalFourthData.Bq 6387
    have hp : val WuPaper.ClassicalFourthData.Bq 6387 = (265311924133130:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6387 = 265311924133130 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6387 = (14387:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6387
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6388) ≤ val WuPaper.ClassicalFourthData.Bq 6388
    have hp : val WuPaper.ClassicalFourthData.Bq 6388 = (265320248173662:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6388 = 265320248173662 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6388 = (3597:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6388
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6389) ≤ val WuPaper.ClassicalFourthData.Bq 6389
    have hp : val WuPaper.ClassicalFourthData.Bq 6389 = (265328568481078:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6389 = 265328568481078 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6389 = (14389:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6389
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6390) ≤ val WuPaper.ClassicalFourthData.Bq 6390
    have hp : val WuPaper.ClassicalFourthData.Bq 6390 = (265336885056650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6390 = 265336885056650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6390 = (1439:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6390
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6391) ≤ val WuPaper.ClassicalFourthData.Bq 6391
    have hp : val WuPaper.ClassicalFourthData.Bq 6391 = (265345197901653:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6391 = 265345197901653 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6391 = (14391:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6391
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6392) ≤ val WuPaper.ClassicalFourthData.Bq 6392
    have hp : val WuPaper.ClassicalFourthData.Bq 6392 = (265353507017360:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6392 = 265353507017360 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6392 = (1799:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6392
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6393) ≤ val WuPaper.ClassicalFourthData.Bq 6393
    have hp : val WuPaper.ClassicalFourthData.Bq 6393 = (265361812405043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6393 = 265361812405043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6393 = (14393:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6393
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6394) ≤ val WuPaper.ClassicalFourthData.Bq 6394
    have hp : val WuPaper.ClassicalFourthData.Bq 6394 = (265370114065975:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6394 = 265370114065975 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6394 = (7197:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6394
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6395) ≤ val WuPaper.ClassicalFourthData.Bq 6395
    have hp : val WuPaper.ClassicalFourthData.Bq 6395 = (265378412001428:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6395 = 265378412001428 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6395 = (2879:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6395
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6396) ≤ val WuPaper.ClassicalFourthData.Bq 6396
    have hp : val WuPaper.ClassicalFourthData.Bq 6396 = (265386706212672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6396 = 265386706212672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6396 = (3599:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6396
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6397) ≤ val WuPaper.ClassicalFourthData.Bq 6397
    have hp : val WuPaper.ClassicalFourthData.Bq 6397 = (265394996700978:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6397 = 265394996700978 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6397 = (14397:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6397
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6398) ≤ val WuPaper.ClassicalFourthData.Bq 6398
    have hp : val WuPaper.ClassicalFourthData.Bq 6398 = (265403283467617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6398 = 265403283467617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6398 = (7199:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6398
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6399) ≤ val WuPaper.ClassicalFourthData.Bq 6399
    have hp : val WuPaper.ClassicalFourthData.Bq 6399 = (265411566513858:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6399 = 265411566513858 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6399 = (14399:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6399
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_399
