import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints574
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_574 (j : Fin 16) (hj : 16*574+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*574+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*574+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9184) ≤ val WuPaper.ClassicalFourthData.Bq 9184
    have hp : val WuPaper.ClassicalFourthData.Bq 9184 = (277632591264421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9184 = 277632591264421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9184 = (537:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9184
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9185) ≤ val WuPaper.ClassicalFourthData.Bq 9185
    have hp : val WuPaper.ClassicalFourthData.Bq 9185 = (277634089894706:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9185 = 277634089894706 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9185 = (3437:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9185
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9186) ≤ val WuPaper.ClassicalFourthData.Bq 9186
    have hp : val WuPaper.ClassicalFourthData.Bq 9186 = (277635587011761:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9186 = 277635587011761 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9186 = (8593:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9186
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9187) ≤ val WuPaper.ClassicalFourthData.Bq 9187
    have hp : val WuPaper.ClassicalFourthData.Bq 9187 = (277637082616054:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9187 = 277637082616054 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9187 = (17187:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9187
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9188) ≤ val WuPaper.ClassicalFourthData.Bq 9188
    have hp : val WuPaper.ClassicalFourthData.Bq 9188 = (277638576708051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9188 = 277638576708051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9188 = (4297:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9188
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9189) ≤ val WuPaper.ClassicalFourthData.Bq 9189
    have hp : val WuPaper.ClassicalFourthData.Bq 9189 = (277640069288220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9189 = 277640069288220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9189 = (17189:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9189
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9190) ≤ val WuPaper.ClassicalFourthData.Bq 9190
    have hp : val WuPaper.ClassicalFourthData.Bq 9190 = (277641560357027:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9190 = 277641560357027 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9190 = (1719:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9190
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9191) ≤ val WuPaper.ClassicalFourthData.Bq 9191
    have hp : val WuPaper.ClassicalFourthData.Bq 9191 = (277643049914938:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9191 = 277643049914938 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9191 = (17191:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9191
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9192) ≤ val WuPaper.ClassicalFourthData.Bq 9192
    have hp : val WuPaper.ClassicalFourthData.Bq 9192 = (277644537962421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9192 = 277644537962421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9192 = (2149:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9192
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9193) ≤ val WuPaper.ClassicalFourthData.Bq 9193
    have hp : val WuPaper.ClassicalFourthData.Bq 9193 = (277646024499941:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9193 = 277646024499941 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9193 = (17193:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9193
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9194) ≤ val WuPaper.ClassicalFourthData.Bq 9194
    have hp : val WuPaper.ClassicalFourthData.Bq 9194 = (277647509527964:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9194 = 277647509527964 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9194 = (8597:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9194
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9195) ≤ val WuPaper.ClassicalFourthData.Bq 9195
    have hp : val WuPaper.ClassicalFourthData.Bq 9195 = (277648993046957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9195 = 277648993046957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9195 = (3439:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9195
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9196) ≤ val WuPaper.ClassicalFourthData.Bq 9196
    have hp : val WuPaper.ClassicalFourthData.Bq 9196 = (277650475057385:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9196 = 277650475057385 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9196 = (4299:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9196
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9197) ≤ val WuPaper.ClassicalFourthData.Bq 9197
    have hp : val WuPaper.ClassicalFourthData.Bq 9197 = (277651955559714:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9197 = 277651955559714 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9197 = (17197:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9197
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9198) ≤ val WuPaper.ClassicalFourthData.Bq 9198
    have hp : val WuPaper.ClassicalFourthData.Bq 9198 = (277653434554409:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9198 = 277653434554409 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9198 = (8599:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9198
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9199) ≤ val WuPaper.ClassicalFourthData.Bq 9199
    have hp : val WuPaper.ClassicalFourthData.Bq 9199 = (277654912041936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9199 = 277654912041936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9199 = (17199:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9199
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_574
