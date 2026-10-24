import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints267
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_267 (j : Fin 16) (hj : 16*267+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*267+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*267+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4272) ≤ val WuPaper.ClassicalFourthData.Bq 4272
    have hp : val WuPaper.ClassicalFourthData.Bq 4272 = (236825931110230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4272 = 236825931110230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4272 = (767:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4272
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4273) ≤ val WuPaper.ClassicalFourthData.Bq 4273
    have hp : val WuPaper.ClassicalFourthData.Bq 4273 = (236846032457641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4273 = 236846032457641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4273 = (12273:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4273
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4274) ≤ val WuPaper.ClassicalFourthData.Bq 4274
    have hp : val WuPaper.ClassicalFourthData.Bq 4274 = (236866125768073:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4274 = 236866125768073 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4274 = (6137:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4274
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4275) ≤ val WuPaper.ClassicalFourthData.Bq 4275
    have hp : val WuPaper.ClassicalFourthData.Bq 4275 = (236886211044640:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4275 = 236886211044640 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4275 = (491:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4275
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4276) ≤ val WuPaper.ClassicalFourthData.Bq 4276
    have hp : val WuPaper.ClassicalFourthData.Bq 4276 = (236906288290455:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4276 = 236906288290455 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4276 = (3069:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4276
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4277) ≤ val WuPaper.ClassicalFourthData.Bq 4277
    have hp : val WuPaper.ClassicalFourthData.Bq 4277 = (236926357508632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4277 = 236926357508632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4277 = (12277:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4277
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4278) ≤ val WuPaper.ClassicalFourthData.Bq 4278
    have hp : val WuPaper.ClassicalFourthData.Bq 4278 = (236946418702281:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4278 = 236946418702281 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4278 = (6139:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4278
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4279) ≤ val WuPaper.ClassicalFourthData.Bq 4279
    have hp : val WuPaper.ClassicalFourthData.Bq 4279 = (236966471874511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4279 = 236966471874511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4279 = (12279:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4279
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4280) ≤ val WuPaper.ClassicalFourthData.Bq 4280
    have hp : val WuPaper.ClassicalFourthData.Bq 4280 = (236986517028430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4280 = 236986517028430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4280 = (307:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4280
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4281) ≤ val WuPaper.ClassicalFourthData.Bq 4281
    have hp : val WuPaper.ClassicalFourthData.Bq 4281 = (237006554167144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4281 = 237006554167144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4281 = (12281:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4281
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4282) ≤ val WuPaper.ClassicalFourthData.Bq 4282
    have hp : val WuPaper.ClassicalFourthData.Bq 4282 = (237026583293759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4282 = 237026583293759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4282 = (6141:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4282
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4283) ≤ val WuPaper.ClassicalFourthData.Bq 4283
    have hp : val WuPaper.ClassicalFourthData.Bq 4283 = (237046604411378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4283 = 237046604411378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4283 = (12283:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4283
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4284) ≤ val WuPaper.ClassicalFourthData.Bq 4284
    have hp : val WuPaper.ClassicalFourthData.Bq 4284 = (237066617523103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4284 = 237066617523103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4284 = (3071:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4284
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4285) ≤ val WuPaper.ClassicalFourthData.Bq 4285
    have hp : val WuPaper.ClassicalFourthData.Bq 4285 = (237086622632035:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4285 = 237086622632035 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4285 = (2457:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4285
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4286) ≤ val WuPaper.ClassicalFourthData.Bq 4286
    have hp : val WuPaper.ClassicalFourthData.Bq 4286 = (237106619741273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4286 = 237106619741273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4286 = (6143:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4286
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4287) ≤ val WuPaper.ClassicalFourthData.Bq 4287
    have hp : val WuPaper.ClassicalFourthData.Bq 4287 = (237126608853916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4287 = 237126608853916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4287 = (12287:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4287
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_267
