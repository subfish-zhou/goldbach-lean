import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints270
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_270 (j : Fin 16) (hj : 16*270+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*270+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*270+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4320) ≤ val WuPaper.ClassicalFourthData.Bq 4320
    have hp : val WuPaper.ClassicalFourthData.Bq 4320 = (237781783673126:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4320 = 237781783673126 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4320 = (77:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4320
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4321) ≤ val WuPaper.ClassicalFourthData.Bq 4321
    have hp : val WuPaper.ClassicalFourthData.Bq 4321 = (237801502734649:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4321 = 237801502734649 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4321 = (12321:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4321
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4322) ≤ val WuPaper.ClassicalFourthData.Bq 4322
    have hp : val WuPaper.ClassicalFourthData.Bq 4322 = (237821213907113:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4322 = 237821213907113 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4322 = (6161:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4322
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4323) ≤ val WuPaper.ClassicalFourthData.Bq 4323
    have hp : val WuPaper.ClassicalFourthData.Bq 4323 = (237840917193563:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4323 = 237840917193563 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4323 = (12323:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4323
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4324) ≤ val WuPaper.ClassicalFourthData.Bq 4324
    have hp : val WuPaper.ClassicalFourthData.Bq 4324 = (237860612597046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4324 = 237860612597046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4324 = (3081:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4324
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4325) ≤ val WuPaper.ClassicalFourthData.Bq 4325
    have hp : val WuPaper.ClassicalFourthData.Bq 4325 = (237880300120606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4325 = 237880300120606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4325 = (493:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4325
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4326) ≤ val WuPaper.ClassicalFourthData.Bq 4326
    have hp : val WuPaper.ClassicalFourthData.Bq 4326 = (237899979767287:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4326 = 237899979767287 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4326 = (6163:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4326
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4327) ≤ val WuPaper.ClassicalFourthData.Bq 4327
    have hp : val WuPaper.ClassicalFourthData.Bq 4327 = (237919651540129:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4327 = 237919651540129 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4327 = (12327:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4327
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4328) ≤ val WuPaper.ClassicalFourthData.Bq 4328
    have hp : val WuPaper.ClassicalFourthData.Bq 4328 = (237939315442173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4328 = 237939315442173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4328 = (1541:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4328
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4329) ≤ val WuPaper.ClassicalFourthData.Bq 4329
    have hp : val WuPaper.ClassicalFourthData.Bq 4329 = (237958971476459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4329 = 237958971476459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4329 = (12329:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4329
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4330) ≤ val WuPaper.ClassicalFourthData.Bq 4330
    have hp : val WuPaper.ClassicalFourthData.Bq 4330 = (237978619646022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4330 = 237978619646022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4330 = (1233:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4330
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4331) ≤ val WuPaper.ClassicalFourthData.Bq 4331
    have hp : val WuPaper.ClassicalFourthData.Bq 4331 = (237998259953899:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4331 = 237998259953899 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4331 = (12331:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4331
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4332) ≤ val WuPaper.ClassicalFourthData.Bq 4332
    have hp : val WuPaper.ClassicalFourthData.Bq 4332 = (238017892403126:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4332 = 238017892403126 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4332 = (3083:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4332
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4333) ≤ val WuPaper.ClassicalFourthData.Bq 4333
    have hp : val WuPaper.ClassicalFourthData.Bq 4333 = (238037516996734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4333 = 238037516996734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4333 = (12333:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4333
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4334) ≤ val WuPaper.ClassicalFourthData.Bq 4334
    have hp : val WuPaper.ClassicalFourthData.Bq 4334 = (238057133737757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4334 = 238057133737757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4334 = (6167:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4334
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4335) ≤ val WuPaper.ClassicalFourthData.Bq 4335
    have hp : val WuPaper.ClassicalFourthData.Bq 4335 = (238076742629224:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4335 = 238076742629224 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4335 = (2467:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4335
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_270
