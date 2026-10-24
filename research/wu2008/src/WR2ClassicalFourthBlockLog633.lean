import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints633
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_633 (j : Fin 16) (hj : 16*633+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*633+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*633+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10128) ≤ val WuPaper.ClassicalFourthData.Bq 10128
    have hp : val WuPaper.ClassicalFourthData.Bq 10128 = (278434307779739:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10128 = 278434307779739 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10128 = (1133:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10128
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10129) ≤ val WuPaper.ClassicalFourthData.Bq 10129
    have hp : val WuPaper.ClassicalFourthData.Bq 10129 = (278434566005852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10129 = 278434566005852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10129 = (18129:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10129
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10130) ≤ val WuPaper.ClassicalFourthData.Bq 10130
    have hp : val WuPaper.ClassicalFourthData.Bq 10130 = (278434823098282:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10130 = 278434823098282 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10130 = (1813:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10130
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10131) ≤ val WuPaper.ClassicalFourthData.Bq 10131
    have hp : val WuPaper.ClassicalFourthData.Bq 10131 = (278435079057375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10131 = 278435079057375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10131 = (18131:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10131
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10132) ≤ val WuPaper.ClassicalFourthData.Bq 10132
    have hp : val WuPaper.ClassicalFourthData.Bq 10132 = (278435333883473:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10132 = 278435333883473 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10132 = (4533:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10132
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10133) ≤ val WuPaper.ClassicalFourthData.Bq 10133
    have hp : val WuPaper.ClassicalFourthData.Bq 10133 = (278435587576921:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10133 = 278435587576921 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10133 = (18133:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10133
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10134) ≤ val WuPaper.ClassicalFourthData.Bq 10134
    have hp : val WuPaper.ClassicalFourthData.Bq 10134 = (278435840138063:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10134 = 278435840138063 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10134 = (9067:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10134
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10135) ≤ val WuPaper.ClassicalFourthData.Bq 10135
    have hp : val WuPaper.ClassicalFourthData.Bq 10135 = (278436091567241:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10135 = 278436091567241 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10135 = (3627:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10135
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10136) ≤ val WuPaper.ClassicalFourthData.Bq 10136
    have hp : val WuPaper.ClassicalFourthData.Bq 10136 = (278436341864799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10136 = 278436341864799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10136 = (2267:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10136
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10137) ≤ val WuPaper.ClassicalFourthData.Bq 10137
    have hp : val WuPaper.ClassicalFourthData.Bq 10137 = (278436591031081:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10137 = 278436591031081 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10137 = (18137:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10137
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10138) ≤ val WuPaper.ClassicalFourthData.Bq 10138
    have hp : val WuPaper.ClassicalFourthData.Bq 10138 = (278436839066430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10138 = 278436839066430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10138 = (9069:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10138
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10139) ≤ val WuPaper.ClassicalFourthData.Bq 10139
    have hp : val WuPaper.ClassicalFourthData.Bq 10139 = (278437085971189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10139 = 278437085971189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10139 = (18139:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10139
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10140) ≤ val WuPaper.ClassicalFourthData.Bq 10140
    have hp : val WuPaper.ClassicalFourthData.Bq 10140 = (278437331745700:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10140 = 278437331745700 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10140 = (907:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10140
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10141) ≤ val WuPaper.ClassicalFourthData.Bq 10141
    have hp : val WuPaper.ClassicalFourthData.Bq 10141 = (278437576390308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10141 = 278437576390308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10141 = (18141:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10141
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10142) ≤ val WuPaper.ClassicalFourthData.Bq 10142
    have hp : val WuPaper.ClassicalFourthData.Bq 10142 = (278437819905355:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10142 = 278437819905355 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10142 = (9071:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10142
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10143) ≤ val WuPaper.ClassicalFourthData.Bq 10143
    have hp : val WuPaper.ClassicalFourthData.Bq 10143 = (278438062291183:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10143 = 278438062291183 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10143 = (18143:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10143
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_633
