import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints636
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_636 (j : Fin 16) (hj : 16*636+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*636+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*636+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10176) ≤ val WuPaper.ClassicalFourthData.Bq 10176
    have hp : val WuPaper.ClassicalFourthData.Bq 10176 = (278445429768426:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10176 = 278445429768426 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10176 = (568:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10176
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10177) ≤ val WuPaper.ClassicalFourthData.Bq 10177
    have hp : val WuPaper.ClassicalFourthData.Bq 10177 = (278445633963952:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10177 = 278445633963952 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10177 = (18177:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10177
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10178) ≤ val WuPaper.ClassicalFourthData.Bq 10178
    have hp : val WuPaper.ClassicalFourthData.Bq 10178 = (278445837042185:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10178 = 278445837042185 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10178 = (9089:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10178
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10179) ≤ val WuPaper.ClassicalFourthData.Bq 10179
    have hp : val WuPaper.ClassicalFourthData.Bq 10179 = (278446039003465:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10179 = 278446039003465 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10179 = (18179:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10179
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10180) ≤ val WuPaper.ClassicalFourthData.Bq 10180
    have hp : val WuPaper.ClassicalFourthData.Bq 10180 = (278446239848130:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10180 = 278446239848130 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10180 = (909:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10180
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10181) ≤ val WuPaper.ClassicalFourthData.Bq 10181
    have hp : val WuPaper.ClassicalFourthData.Bq 10181 = (278446439576518:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10181 = 278446439576518 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10181 = (18181:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10181
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10182) ≤ val WuPaper.ClassicalFourthData.Bq 10182
    have hp : val WuPaper.ClassicalFourthData.Bq 10182 = (278446638188968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10182 = 278446638188968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10182 = (9091:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10182
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10183) ≤ val WuPaper.ClassicalFourthData.Bq 10183
    have hp : val WuPaper.ClassicalFourthData.Bq 10183 = (278446835685819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10183 = 278446835685819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10183 = (18183:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10183
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10184) ≤ val WuPaper.ClassicalFourthData.Bq 10184
    have hp : val WuPaper.ClassicalFourthData.Bq 10184 = (278447032067409:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10184 = 278447032067409 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10184 = (2273:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10184
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10185) ≤ val WuPaper.ClassicalFourthData.Bq 10185
    have hp : val WuPaper.ClassicalFourthData.Bq 10185 = (278447227334076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10185 = 278447227334076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10185 = (3637:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10185
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10186) ≤ val WuPaper.ClassicalFourthData.Bq 10186
    have hp : val WuPaper.ClassicalFourthData.Bq 10186 = (278447421486158:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10186 = 278447421486158 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10186 = (9093:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10186
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10187) ≤ val WuPaper.ClassicalFourthData.Bq 10187
    have hp : val WuPaper.ClassicalFourthData.Bq 10187 = (278447614523992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10187 = 278447614523992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10187 = (18187:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10187
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10188) ≤ val WuPaper.ClassicalFourthData.Bq 10188
    have hp : val WuPaper.ClassicalFourthData.Bq 10188 = (278447806447918:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10188 = 278447806447918 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10188 = (4547:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10188
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10189) ≤ val WuPaper.ClassicalFourthData.Bq 10189
    have hp : val WuPaper.ClassicalFourthData.Bq 10189 = (278447997258272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10189 = 278447997258272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10189 = (18189:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10189
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10190) ≤ val WuPaper.ClassicalFourthData.Bq 10190
    have hp : val WuPaper.ClassicalFourthData.Bq 10190 = (278448186955392:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10190 = 278448186955392 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10190 = (1819:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10190
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10191) ≤ val WuPaper.ClassicalFourthData.Bq 10191
    have hp : val WuPaper.ClassicalFourthData.Bq 10191 = (278448375539616:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10191 = 278448375539616 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10191 = (18191:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_636
