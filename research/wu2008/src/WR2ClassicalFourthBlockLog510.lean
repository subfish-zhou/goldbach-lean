import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints510
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_510 (j : Fin 16) (hj : 16*510+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*510+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*510+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8160) ≤ val WuPaper.ClassicalFourthData.Bq 8160
    have hp : val WuPaper.ClassicalFourthData.Bq 8160 = (275212256292497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8160 = 275212256292497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8160 = (101:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8160
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8161) ≤ val WuPaper.ClassicalFourthData.Bq 8161
    have hp : val WuPaper.ClassicalFourthData.Bq 8161 = (275215580442432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8161 = 275215580442432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8161 = (16161:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8161
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8162) ≤ val WuPaper.ClassicalFourthData.Bq 8162
    have hp : val WuPaper.ClassicalFourthData.Bq 8162 = (275218902507511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8162 = 275218902507511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8162 = (8081:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8162
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8163) ≤ val WuPaper.ClassicalFourthData.Bq 8163
    have hp : val WuPaper.ClassicalFourthData.Bq 8163 = (275222222488397:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8163 = 275222222488397 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8163 = (16163:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8163
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8164) ≤ val WuPaper.ClassicalFourthData.Bq 8164
    have hp : val WuPaper.ClassicalFourthData.Bq 8164 = (275225540385750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8164 = 275225540385750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8164 = (4041:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8164
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8165) ≤ val WuPaper.ClassicalFourthData.Bq 8165
    have hp : val WuPaper.ClassicalFourthData.Bq 8165 = (275228856200232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8165 = 275228856200232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8165 = (3233:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8165
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8166) ≤ val WuPaper.ClassicalFourthData.Bq 8166
    have hp : val WuPaper.ClassicalFourthData.Bq 8166 = (275232169932506:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8166 = 275232169932506 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8166 = (8083:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8166
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8167) ≤ val WuPaper.ClassicalFourthData.Bq 8167
    have hp : val WuPaper.ClassicalFourthData.Bq 8167 = (275235481583233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8167 = 275235481583233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8167 = (16167:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8167
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8168) ≤ val WuPaper.ClassicalFourthData.Bq 8168
    have hp : val WuPaper.ClassicalFourthData.Bq 8168 = (275238791153072:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8168 = 275238791153072 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8168 = (2021:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8168
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8169) ≤ val WuPaper.ClassicalFourthData.Bq 8169
    have hp : val WuPaper.ClassicalFourthData.Bq 8169 = (275242098642686:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8169 = 275242098642686 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8169 = (16169:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8169
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8170) ≤ val WuPaper.ClassicalFourthData.Bq 8170
    have hp : val WuPaper.ClassicalFourthData.Bq 8170 = (275245404052734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8170 = 275245404052734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8170 = (1617:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8170
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8171) ≤ val WuPaper.ClassicalFourthData.Bq 8171
    have hp : val WuPaper.ClassicalFourthData.Bq 8171 = (275248707383877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8171 = 275248707383877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8171 = (16171:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8171
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8172) ≤ val WuPaper.ClassicalFourthData.Bq 8172
    have hp : val WuPaper.ClassicalFourthData.Bq 8172 = (275252008636775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8172 = 275252008636775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8172 = (4043:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8172
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8173) ≤ val WuPaper.ClassicalFourthData.Bq 8173
    have hp : val WuPaper.ClassicalFourthData.Bq 8173 = (275255307812087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8173 = 275255307812087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8173 = (16173:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8173
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8174) ≤ val WuPaper.ClassicalFourthData.Bq 8174
    have hp : val WuPaper.ClassicalFourthData.Bq 8174 = (275258604910474:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8174 = 275258604910474 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8174 = (8087:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8174
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8175) ≤ val WuPaper.ClassicalFourthData.Bq 8175
    have hp : val WuPaper.ClassicalFourthData.Bq 8175 = (275261899932595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8175 = 275261899932595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8175 = (647:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8175
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_510
