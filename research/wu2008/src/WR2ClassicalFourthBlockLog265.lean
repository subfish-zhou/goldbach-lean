import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints265
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_265 (j : Fin 16) (hj : 16*265+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*265+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*265+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4240) ≤ val WuPaper.ClassicalFourthData.Bq 4240
    have hp : val WuPaper.ClassicalFourthData.Bq 4240 = (236178425752121:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4240 = 236178425752121 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4240 = (153:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4240
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4241) ≤ val WuPaper.ClassicalFourthData.Bq 4241
    have hp : val WuPaper.ClassicalFourthData.Bq 4241 = (236198785936233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4241 = 236198785936233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4241 = (12241:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4241
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4242) ≤ val WuPaper.ClassicalFourthData.Bq 4242
    have hp : val WuPaper.ClassicalFourthData.Bq 4242 = (236219137982923:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4242 = 236219137982923 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4242 = (6121:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4242
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4243) ≤ val WuPaper.ClassicalFourthData.Bq 4243
    have hp : val WuPaper.ClassicalFourthData.Bq 4243 = (236239481895353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4243 = 236239481895353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4243 = (12243:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4243
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4244) ≤ val WuPaper.ClassicalFourthData.Bq 4244
    have hp : val WuPaper.ClassicalFourthData.Bq 4244 = (236259817676682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4244 = 236259817676682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4244 = (3061:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4244
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4245) ≤ val WuPaper.ClassicalFourthData.Bq 4245
    have hp : val WuPaper.ClassicalFourthData.Bq 4245 = (236280145330069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4245 = 236280145330069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4245 = (2449:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4245
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4246) ≤ val WuPaper.ClassicalFourthData.Bq 4246
    have hp : val WuPaper.ClassicalFourthData.Bq 4246 = (236300464858670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4246 = 236300464858670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4246 = (6123:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4246
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4247) ≤ val WuPaper.ClassicalFourthData.Bq 4247
    have hp : val WuPaper.ClassicalFourthData.Bq 4247 = (236320776265642:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4247 = 236320776265642 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4247 = (12247:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4247
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4248) ≤ val WuPaper.ClassicalFourthData.Bq 4248
    have hp : val WuPaper.ClassicalFourthData.Bq 4248 = (236341079554138:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4248 = 236341079554138 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4248 = (1531:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4248
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4249) ≤ val WuPaper.ClassicalFourthData.Bq 4249
    have hp : val WuPaper.ClassicalFourthData.Bq 4249 = (236361374727310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4249 = 236361374727310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4249 = (12249:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4249
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4250) ≤ val WuPaper.ClassicalFourthData.Bq 4250
    have hp : val WuPaper.ClassicalFourthData.Bq 4250 = (236381661788310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4250 = 236381661788310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4250 = (49:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4250
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4251) ≤ val WuPaper.ClassicalFourthData.Bq 4251
    have hp : val WuPaper.ClassicalFourthData.Bq 4251 = (236401940740288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4251 = 236401940740288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4251 = (12251:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4251
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4252) ≤ val WuPaper.ClassicalFourthData.Bq 4252
    have hp : val WuPaper.ClassicalFourthData.Bq 4252 = (236422211586391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4252 = 236422211586391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4252 = (3063:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4252
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4253) ≤ val WuPaper.ClassicalFourthData.Bq 4253
    have hp : val WuPaper.ClassicalFourthData.Bq 4253 = (236442474329767:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4253 = 236442474329767 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4253 = (12253:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4253
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4254) ≤ val WuPaper.ClassicalFourthData.Bq 4254
    have hp : val WuPaper.ClassicalFourthData.Bq 4254 = (236462728973560:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4254 = 236462728973560 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4254 = (6127:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4254
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4255) ≤ val WuPaper.ClassicalFourthData.Bq 4255
    have hp : val WuPaper.ClassicalFourthData.Bq 4255 = (236482975520915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4255 = 236482975520915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4255 = (2451:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_265
