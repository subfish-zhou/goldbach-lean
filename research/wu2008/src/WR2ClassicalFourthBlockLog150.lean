import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints150
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_150 (j : Fin 16) (hj : 16*150+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*150+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*150+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2400) ≤ val WuPaper.ClassicalFourthData.Bq 2400
    have hp : val WuPaper.ClassicalFourthData.Bq 2400 = (180770626632976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2400 = 180770626632976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2400 = (13:ℝ)/5 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2400
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2401) ≤ val WuPaper.ClassicalFourthData.Bq 2401
    have hp : val WuPaper.ClassicalFourthData.Bq 2401 = (180813332194972:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2401 = 180813332194972 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2401 = (10401:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2401
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2402) ≤ val WuPaper.ClassicalFourthData.Bq 2402
    have hp : val WuPaper.ClassicalFourthData.Bq 2402 = (180856020160654:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2402 = 180856020160654 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2402 = (5201:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2402
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2403) ≤ val WuPaper.ClassicalFourthData.Bq 2403
    have hp : val WuPaper.ClassicalFourthData.Bq 2403 = (180898690538028:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2403 = 180898690538028 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2403 = (10403:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2403
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2404) ≤ val WuPaper.ClassicalFourthData.Bq 2404
    have hp : val WuPaper.ClassicalFourthData.Bq 2404 = (180941343335094:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2404 = 180941343335094 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2404 = (2601:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2404
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2405) ≤ val WuPaper.ClassicalFourthData.Bq 2405
    have hp : val WuPaper.ClassicalFourthData.Bq 2405 = (180983978559849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2405 = 180983978559849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2405 = (2081:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2405
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2406) ≤ val WuPaper.ClassicalFourthData.Bq 2406
    have hp : val WuPaper.ClassicalFourthData.Bq 2406 = (181026596220287:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2406 = 181026596220287 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2406 = (5203:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2406
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2407) ≤ val WuPaper.ClassicalFourthData.Bq 2407
    have hp : val WuPaper.ClassicalFourthData.Bq 2407 = (181069196324395:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2407 = 181069196324395 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2407 = (10407:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2407
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2408) ≤ val WuPaper.ClassicalFourthData.Bq 2408
    have hp : val WuPaper.ClassicalFourthData.Bq 2408 = (181111778880157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2408 = 181111778880157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2408 = (1301:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2408
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2409) ≤ val WuPaper.ClassicalFourthData.Bq 2409
    have hp : val WuPaper.ClassicalFourthData.Bq 2409 = (181154343895552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2409 = 181154343895552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2409 = (10409:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2409
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2410) ≤ val WuPaper.ClassicalFourthData.Bq 2410
    have hp : val WuPaper.ClassicalFourthData.Bq 2410 = (181196891378555:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2410 = 181196891378555 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2410 = (1041:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2410
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2411) ≤ val WuPaper.ClassicalFourthData.Bq 2411
    have hp : val WuPaper.ClassicalFourthData.Bq 2411 = (181239421337136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2411 = 181239421337136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2411 = (10411:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2411
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2412) ≤ val WuPaper.ClassicalFourthData.Bq 2412
    have hp : val WuPaper.ClassicalFourthData.Bq 2412 = (181281933779261:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2412 = 181281933779261 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2412 = (2603:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2412
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2413) ≤ val WuPaper.ClassicalFourthData.Bq 2413
    have hp : val WuPaper.ClassicalFourthData.Bq 2413 = (181324428712892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2413 = 181324428712892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2413 = (10413:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2413
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2414) ≤ val WuPaper.ClassicalFourthData.Bq 2414
    have hp : val WuPaper.ClassicalFourthData.Bq 2414 = (181366906145986:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2414 = 181366906145986 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2414 = (5207:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2414
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2415) ≤ val WuPaper.ClassicalFourthData.Bq 2415
    have hp : val WuPaper.ClassicalFourthData.Bq 2415 = (181409366086495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2415 = 181409366086495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2415 = (2083:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2415
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_150
