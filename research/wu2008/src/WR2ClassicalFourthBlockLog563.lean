import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints563
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_563 (j : Fin 16) (hj : 16*563+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*563+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*563+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9008) ≤ val WuPaper.ClassicalFourthData.Bq 9008
    have hp : val WuPaper.ClassicalFourthData.Bq 9008 = (277344824013091:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9008 = 277344824013091 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9008 = (1063:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9008
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9009) ≤ val WuPaper.ClassicalFourthData.Bq 9009
    have hp : val WuPaper.ClassicalFourthData.Bq 9009 = (277346596394300:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9009 = 277346596394300 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9009 = (17009:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9009
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9010) ≤ val WuPaper.ClassicalFourthData.Bq 9010
    have hp : val WuPaper.ClassicalFourthData.Bq 9010 = (277348367177587:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9010 = 277348367177587 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9010 = (1701:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9010
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9011) ≤ val WuPaper.ClassicalFourthData.Bq 9011
    have hp : val WuPaper.ClassicalFourthData.Bq 9011 = (277350136363446:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9011 = 277350136363446 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9011 = (17011:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9011
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9012) ≤ val WuPaper.ClassicalFourthData.Bq 9012
    have hp : val WuPaper.ClassicalFourthData.Bq 9012 = (277351903952373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9012 = 277351903952373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9012 = (4253:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9012
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9013) ≤ val WuPaper.ClassicalFourthData.Bq 9013
    have hp : val WuPaper.ClassicalFourthData.Bq 9013 = (277353669944864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9013 = 277353669944864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9013 = (17013:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9013
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9014) ≤ val WuPaper.ClassicalFourthData.Bq 9014
    have hp : val WuPaper.ClassicalFourthData.Bq 9014 = (277355434341412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9014 = 277355434341412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9014 = (8507:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9014
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9015) ≤ val WuPaper.ClassicalFourthData.Bq 9015
    have hp : val WuPaper.ClassicalFourthData.Bq 9015 = (277357197142513:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9015 = 277357197142513 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9015 = (3403:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9015
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9016) ≤ val WuPaper.ClassicalFourthData.Bq 9016
    have hp : val WuPaper.ClassicalFourthData.Bq 9016 = (277358958348662:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9016 = 277358958348662 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9016 = (2127:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9016
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9017) ≤ val WuPaper.ClassicalFourthData.Bq 9017
    have hp : val WuPaper.ClassicalFourthData.Bq 9017 = (277360717960352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9017 = 277360717960352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9017 = (17017:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9017
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9018) ≤ val WuPaper.ClassicalFourthData.Bq 9018
    have hp : val WuPaper.ClassicalFourthData.Bq 9018 = (277362475978078:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9018 = 277362475978078 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9018 = (8509:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9018
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9019) ≤ val WuPaper.ClassicalFourthData.Bq 9019
    have hp : val WuPaper.ClassicalFourthData.Bq 9019 = (277364232402334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9019 = 277364232402334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9019 = (17019:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9019
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9020) ≤ val WuPaper.ClassicalFourthData.Bq 9020
    have hp : val WuPaper.ClassicalFourthData.Bq 9020 = (277365987233613:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9020 = 277365987233613 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9020 = (851:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9020
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9021) ≤ val WuPaper.ClassicalFourthData.Bq 9021
    have hp : val WuPaper.ClassicalFourthData.Bq 9021 = (277367740472411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9021 = 277367740472411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9021 = (17021:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9021
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9022) ≤ val WuPaper.ClassicalFourthData.Bq 9022
    have hp : val WuPaper.ClassicalFourthData.Bq 9022 = (277369492119219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9022 = 277369492119219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9022 = (8511:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9022
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9023) ≤ val WuPaper.ClassicalFourthData.Bq 9023
    have hp : val WuPaper.ClassicalFourthData.Bq 9023 = (277371242174533:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9023 = 277371242174533 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9023 = (17023:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_563
