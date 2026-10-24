import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints577
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_577 (j : Fin 16) (hj : 16*577+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*577+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*577+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9232) ≤ val WuPaper.ClassicalFourthData.Bq 9232
    have hp : val WuPaper.ClassicalFourthData.Bq 9232 = (277702826645388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9232 = 277702826645388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9232 = (1077:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9232
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9233) ≤ val WuPaper.ClassicalFourthData.Bq 9233
    have hp : val WuPaper.ClassicalFourthData.Bq 9233 = (277704253164964:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9233 = 277704253164964 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9233 = (17233:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9233
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9234) ≤ val WuPaper.ClassicalFourthData.Bq 9234
    have hp : val WuPaper.ClassicalFourthData.Bq 9234 = (277705678193561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9234 = 277705678193561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9234 = (8617:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9234
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9235) ≤ val WuPaper.ClassicalFourthData.Bq 9235
    have hp : val WuPaper.ClassicalFourthData.Bq 9235 = (277707101731640:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9235 = 277707101731640 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9235 = (3447:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9235
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9236) ≤ val WuPaper.ClassicalFourthData.Bq 9236
    have hp : val WuPaper.ClassicalFourthData.Bq 9236 = (277708523779659:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9236 = 277708523779659 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9236 = (4309:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9236
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9237) ≤ val WuPaper.ClassicalFourthData.Bq 9237
    have hp : val WuPaper.ClassicalFourthData.Bq 9237 = (277709944338079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9237 = 277709944338079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9237 = (17237:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9237
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9238) ≤ val WuPaper.ClassicalFourthData.Bq 9238
    have hp : val WuPaper.ClassicalFourthData.Bq 9238 = (277711363407358:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9238 = 277711363407358 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9238 = (8619:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9238
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9239) ≤ val WuPaper.ClassicalFourthData.Bq 9239
    have hp : val WuPaper.ClassicalFourthData.Bq 9239 = (277712780987957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9239 = 277712780987957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9239 = (17239:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9239
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9240) ≤ val WuPaper.ClassicalFourthData.Bq 9240
    have hp : val WuPaper.ClassicalFourthData.Bq 9240 = (277714197080333:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9240 = 277714197080333 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9240 = (431:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9240
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9241) ≤ val WuPaper.ClassicalFourthData.Bq 9241
    have hp : val WuPaper.ClassicalFourthData.Bq 9241 = (277715611684947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9241 = 277715611684947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9241 = (17241:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9241
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9242) ≤ val WuPaper.ClassicalFourthData.Bq 9242
    have hp : val WuPaper.ClassicalFourthData.Bq 9242 = (277717024802256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9242 = 277717024802256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9242 = (8621:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9242
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9243) ≤ val WuPaper.ClassicalFourthData.Bq 9243
    have hp : val WuPaper.ClassicalFourthData.Bq 9243 = (277718436432719:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9243 = 277718436432719 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9243 = (17243:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9243
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9244) ≤ val WuPaper.ClassicalFourthData.Bq 9244
    have hp : val WuPaper.ClassicalFourthData.Bq 9244 = (277719846576795:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9244 = 277719846576795 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9244 = (4311:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9244
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9245) ≤ val WuPaper.ClassicalFourthData.Bq 9245
    have hp : val WuPaper.ClassicalFourthData.Bq 9245 = (277721255234942:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9245 = 277721255234942 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9245 = (3449:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9245
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9246) ≤ val WuPaper.ClassicalFourthData.Bq 9246
    have hp : val WuPaper.ClassicalFourthData.Bq 9246 = (277722662407618:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9246 = 277722662407618 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9246 = (8623:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9246
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9247) ≤ val WuPaper.ClassicalFourthData.Bq 9247
    have hp : val WuPaper.ClassicalFourthData.Bq 9247 = (277724068095282:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9247 = 277724068095282 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9247 = (17247:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9247
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_577
