import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints211
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_211 (j : Fin 16) (hj : 16*211+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*211+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*211+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3376) ≤ val WuPaper.ClassicalFourthData.Bq 3376
    have hp : val WuPaper.ClassicalFourthData.Bq 3376 = (215167765518426:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3376 = 215167765518426 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3376 = (711:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3376
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3377) ≤ val WuPaper.ClassicalFourthData.Bq 3377
    have hp : val WuPaper.ClassicalFourthData.Bq 3377 = (215196516052483:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3377 = 215196516052483 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3377 = (11377:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3377
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3378) ≤ val WuPaper.ClassicalFourthData.Bq 3378
    have hp : val WuPaper.ClassicalFourthData.Bq 3378 = (215225255072805:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3378 = 215225255072805 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3378 = (5689:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3378
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3379) ≤ val WuPaper.ClassicalFourthData.Bq 3379
    have hp : val WuPaper.ClassicalFourthData.Bq 3379 = (215253982584178:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3379 = 215253982584178 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3379 = (11379:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3379
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3380) ≤ val WuPaper.ClassicalFourthData.Bq 3380
    have hp : val WuPaper.ClassicalFourthData.Bq 3380 = (215282698591386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3380 = 215282698591386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3380 = (569:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3380
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3381) ≤ val WuPaper.ClassicalFourthData.Bq 3381
    have hp : val WuPaper.ClassicalFourthData.Bq 3381 = (215311403099210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3381 = 215311403099210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3381 = (11381:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3381
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3382) ≤ val WuPaper.ClassicalFourthData.Bq 3382
    have hp : val WuPaper.ClassicalFourthData.Bq 3382 = (215340096112429:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3382 = 215340096112429 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3382 = (5691:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3382
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3383) ≤ val WuPaper.ClassicalFourthData.Bq 3383
    have hp : val WuPaper.ClassicalFourthData.Bq 3383 = (215368777635822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3383 = 215368777635822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3383 = (11383:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3383
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3384) ≤ val WuPaper.ClassicalFourthData.Bq 3384
    have hp : val WuPaper.ClassicalFourthData.Bq 3384 = (215397447674161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3384 = 215397447674161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3384 = (1423:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3384
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3385) ≤ val WuPaper.ClassicalFourthData.Bq 3385
    have hp : val WuPaper.ClassicalFourthData.Bq 3385 = (215426106232219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3385 = 215426106232219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3385 = (2277:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3385
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3386) ≤ val WuPaper.ClassicalFourthData.Bq 3386
    have hp : val WuPaper.ClassicalFourthData.Bq 3386 = (215454753314766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3386 = 215454753314766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3386 = (5693:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3386
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3387) ≤ val WuPaper.ClassicalFourthData.Bq 3387
    have hp : val WuPaper.ClassicalFourthData.Bq 3387 = (215483388926569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3387 = 215483388926569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3387 = (11387:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3387
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3388) ≤ val WuPaper.ClassicalFourthData.Bq 3388
    have hp : val WuPaper.ClassicalFourthData.Bq 3388 = (215512013072394:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3388 = 215512013072394 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3388 = (2847:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3388
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3389) ≤ val WuPaper.ClassicalFourthData.Bq 3389
    have hp : val WuPaper.ClassicalFourthData.Bq 3389 = (215540625757001:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3389 = 215540625757001 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3389 = (11389:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3389
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3390) ≤ val WuPaper.ClassicalFourthData.Bq 3390
    have hp : val WuPaper.ClassicalFourthData.Bq 3390 = (215569226985152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3390 = 215569226985152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3390 = (1139:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3390
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3391) ≤ val WuPaper.ClassicalFourthData.Bq 3391
    have hp : val WuPaper.ClassicalFourthData.Bq 3391 = (215597816761605:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3391 = 215597816761605 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3391 = (11391:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3391
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_211
