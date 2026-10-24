import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints321
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_321 (j : Fin 16) (hj : 16*321+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*321+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*321+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5136) ≤ val WuPaper.ClassicalFourthData.Bq 5136
    have hp : val WuPaper.ClassicalFourthData.Bq 5136 = (251500697866555:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5136 = 251500697866555 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5136 = (821:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5136
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5137) ≤ val WuPaper.ClassicalFourthData.Bq 5137
    have hp : val WuPaper.ClassicalFourthData.Bq 5137 = (251514879469162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5137 = 251514879469162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5137 = (13137:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5137
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5138) ≤ val WuPaper.ClassicalFourthData.Bq 5138
    have hp : val WuPaper.ClassicalFourthData.Bq 5138 = (251529055266004:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5138 = 251529055266004 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5138 = (6569:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5138
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5139) ≤ val WuPaper.ClassicalFourthData.Bq 5139
    have hp : val WuPaper.ClassicalFourthData.Bq 5139 = (251543225259206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5139 = 251543225259206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5139 = (13139:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5139
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5140) ≤ val WuPaper.ClassicalFourthData.Bq 5140
    have hp : val WuPaper.ClassicalFourthData.Bq 5140 = (251557389450889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5140 = 251557389450889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5140 = (657:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5140
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5141) ≤ val WuPaper.ClassicalFourthData.Bq 5141
    have hp : val WuPaper.ClassicalFourthData.Bq 5141 = (251571547843176:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5141 = 251571547843176 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5141 = (13141:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5141
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5142) ≤ val WuPaper.ClassicalFourthData.Bq 5142
    have hp : val WuPaper.ClassicalFourthData.Bq 5142 = (251585700438187:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5142 = 251585700438187 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5142 = (6571:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5142
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5143) ≤ val WuPaper.ClassicalFourthData.Bq 5143
    have hp : val WuPaper.ClassicalFourthData.Bq 5143 = (251599847238044:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5143 = 251599847238044 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5143 = (13143:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5143
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5144) ≤ val WuPaper.ClassicalFourthData.Bq 5144
    have hp : val WuPaper.ClassicalFourthData.Bq 5144 = (251613988244864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5144 = 251613988244864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5144 = (1643:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5144
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5145) ≤ val WuPaper.ClassicalFourthData.Bq 5145
    have hp : val WuPaper.ClassicalFourthData.Bq 5145 = (251628123460766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5145 = 251628123460766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5145 = (2629:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5145
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5146) ≤ val WuPaper.ClassicalFourthData.Bq 5146
    have hp : val WuPaper.ClassicalFourthData.Bq 5146 = (251642252887867:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5146 = 251642252887867 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5146 = (6573:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5146
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5147) ≤ val WuPaper.ClassicalFourthData.Bq 5147
    have hp : val WuPaper.ClassicalFourthData.Bq 5147 = (251656376528285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5147 = 251656376528285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5147 = (13147:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5147
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5148) ≤ val WuPaper.ClassicalFourthData.Bq 5148
    have hp : val WuPaper.ClassicalFourthData.Bq 5148 = (251670494384133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5148 = 251670494384133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5148 = (3287:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5148
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5149) ≤ val WuPaper.ClassicalFourthData.Bq 5149
    have hp : val WuPaper.ClassicalFourthData.Bq 5149 = (251684606457528:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5149 = 251684606457528 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5149 = (13149:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5149
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5150) ≤ val WuPaper.ClassicalFourthData.Bq 5150
    have hp : val WuPaper.ClassicalFourthData.Bq 5150 = (251698712750583:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5150 = 251698712750583 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5150 = (263:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5150
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5151) ≤ val WuPaper.ClassicalFourthData.Bq 5151
    have hp : val WuPaper.ClassicalFourthData.Bq 5151 = (251712813265410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5151 = 251712813265410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5151 = (13151:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5151
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_321
