import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints319
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_319 (j : Fin 16) (hj : 16*319+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*319+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*319+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5104) ≤ val WuPaper.ClassicalFourthData.Bq 5104
    have hp : val WuPaper.ClassicalFourthData.Bq 5104 = (251043808383421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5104 = 251043808383421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5104 = (819:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5104
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5105) ≤ val WuPaper.ClassicalFourthData.Bq 5105
    have hp : val WuPaper.ClassicalFourthData.Bq 5105 = (251058176897271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5105 = 251058176897271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5105 = (2621:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5105
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5106) ≤ val WuPaper.ClassicalFourthData.Bq 5106
    have hp : val WuPaper.ClassicalFourthData.Bq 5106 = (251072539536915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5106 = 251072539536915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5106 = (6553:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5106
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5107) ≤ val WuPaper.ClassicalFourthData.Bq 5107
    have hp : val WuPaper.ClassicalFourthData.Bq 5107 = (251086896304507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5107 = 251086896304507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5107 = (13107:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5107
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5108) ≤ val WuPaper.ClassicalFourthData.Bq 5108
    have hp : val WuPaper.ClassicalFourthData.Bq 5108 = (251101247202199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5108 = 251101247202199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5108 = (3277:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5108
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5109) ≤ val WuPaper.ClassicalFourthData.Bq 5109
    have hp : val WuPaper.ClassicalFourthData.Bq 5109 = (251115592232141:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5109 = 251115592232141 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5109 = (13109:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5109
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5110) ≤ val WuPaper.ClassicalFourthData.Bq 5110
    have hp : val WuPaper.ClassicalFourthData.Bq 5110 = (251129931396485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5110 = 251129931396485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5110 = (1311:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5110
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5111) ≤ val WuPaper.ClassicalFourthData.Bq 5111
    have hp : val WuPaper.ClassicalFourthData.Bq 5111 = (251144264697379:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5111 = 251144264697379 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5111 = (13111:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5111
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5112) ≤ val WuPaper.ClassicalFourthData.Bq 5112
    have hp : val WuPaper.ClassicalFourthData.Bq 5112 = (251158592136972:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5112 = 251158592136972 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5112 = (1639:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5112
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5113) ≤ val WuPaper.ClassicalFourthData.Bq 5113
    have hp : val WuPaper.ClassicalFourthData.Bq 5113 = (251172913717411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5113 = 251172913717411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5113 = (13113:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5113
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5114) ≤ val WuPaper.ClassicalFourthData.Bq 5114
    have hp : val WuPaper.ClassicalFourthData.Bq 5114 = (251187229440843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5114 = 251187229440843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5114 = (6557:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5114
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5115) ≤ val WuPaper.ClassicalFourthData.Bq 5115
    have hp : val WuPaper.ClassicalFourthData.Bq 5115 = (251201539309413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5115 = 251201539309413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5115 = (2623:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5115
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5116) ≤ val WuPaper.ClassicalFourthData.Bq 5116
    have hp : val WuPaper.ClassicalFourthData.Bq 5116 = (251215843325267:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5116 = 251215843325267 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5116 = (3279:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5116
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5117) ≤ val WuPaper.ClassicalFourthData.Bq 5117
    have hp : val WuPaper.ClassicalFourthData.Bq 5117 = (251230141490547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5117 = 251230141490547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5117 = (13117:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5117
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5118) ≤ val WuPaper.ClassicalFourthData.Bq 5118
    have hp : val WuPaper.ClassicalFourthData.Bq 5118 = (251244433807398:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5118 = 251244433807398 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5118 = (6559:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5118
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5119) ≤ val WuPaper.ClassicalFourthData.Bq 5119
    have hp : val WuPaper.ClassicalFourthData.Bq 5119 = (251258720277960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5119 = 251258720277960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5119 = (13119:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5119
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_319
