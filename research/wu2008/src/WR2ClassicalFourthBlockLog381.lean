import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints381
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_381 (j : Fin 16) (hj : 16*381+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*381+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*381+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6096) ≤ val WuPaper.ClassicalFourthData.Bq 6096
    have hp : val WuPaper.ClassicalFourthData.Bq 6096 = (262725580215377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6096 = 262725580215377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6096 = (881:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6096
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6097) ≤ val WuPaper.ClassicalFourthData.Bq 6097
    have hp : val WuPaper.ClassicalFourthData.Bq 6097 = (262735046861692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6097 = 262735046861692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6097 = (14097:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6097
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6098) ≤ val WuPaper.ClassicalFourthData.Bq 6098
    have hp : val WuPaper.ClassicalFourthData.Bq 6098 = (262744509381999:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6098 = 262744509381999 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6098 = (7049:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6098
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6099) ≤ val WuPaper.ClassicalFourthData.Bq 6099
    have hp : val WuPaper.ClassicalFourthData.Bq 6099 = (262753967777730:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6099 = 262753967777730 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6099 = (14099:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6099
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6100) ≤ val WuPaper.ClassicalFourthData.Bq 6100
    have hp : val WuPaper.ClassicalFourthData.Bq 6100 = (262763422050311:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6100 = 262763422050311 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6100 = (141:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6100
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6101) ≤ val WuPaper.ClassicalFourthData.Bq 6101
    have hp : val WuPaper.ClassicalFourthData.Bq 6101 = (262772872201172:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6101 = 262772872201172 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6101 = (14101:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6101
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6102) ≤ val WuPaper.ClassicalFourthData.Bq 6102
    have hp : val WuPaper.ClassicalFourthData.Bq 6102 = (262782318231738:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6102 = 262782318231738 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6102 = (7051:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6102
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6103) ≤ val WuPaper.ClassicalFourthData.Bq 6103
    have hp : val WuPaper.ClassicalFourthData.Bq 6103 = (262791760143439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6103 = 262791760143439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6103 = (14103:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6103
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6104) ≤ val WuPaper.ClassicalFourthData.Bq 6104
    have hp : val WuPaper.ClassicalFourthData.Bq 6104 = (262801197937698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6104 = 262801197937698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6104 = (1763:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6104
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6105) ≤ val WuPaper.ClassicalFourthData.Bq 6105
    have hp : val WuPaper.ClassicalFourthData.Bq 6105 = (262810631615943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6105 = 262810631615943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6105 = (2821:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6105
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6106) ≤ val WuPaper.ClassicalFourthData.Bq 6106
    have hp : val WuPaper.ClassicalFourthData.Bq 6106 = (262820061179597:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6106 = 262820061179597 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6106 = (7053:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6106
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6107) ≤ val WuPaper.ClassicalFourthData.Bq 6107
    have hp : val WuPaper.ClassicalFourthData.Bq 6107 = (262829486630087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6107 = 262829486630087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6107 = (14107:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6107
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6108) ≤ val WuPaper.ClassicalFourthData.Bq 6108
    have hp : val WuPaper.ClassicalFourthData.Bq 6108 = (262838907968835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6108 = 262838907968835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6108 = (3527:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6108
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6109) ≤ val WuPaper.ClassicalFourthData.Bq 6109
    have hp : val WuPaper.ClassicalFourthData.Bq 6109 = (262848325197265:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6109 = 262848325197265 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6109 = (14109:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6109
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6110) ≤ val WuPaper.ClassicalFourthData.Bq 6110
    have hp : val WuPaper.ClassicalFourthData.Bq 6110 = (262857738316801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6110 = 262857738316801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6110 = (1411:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6110
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6111) ≤ val WuPaper.ClassicalFourthData.Bq 6111
    have hp : val WuPaper.ClassicalFourthData.Bq 6111 = (262867147328863:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6111 = 262867147328863 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6111 = (14111:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_381
