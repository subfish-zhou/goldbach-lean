import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints526
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_526 (j : Fin 16) (hj : 16*526+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*526+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*526+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8416) ≤ val WuPaper.ClassicalFourthData.Bq 8416
    have hp : val WuPaper.ClassicalFourthData.Bq 8416 = (275996979124493:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8416 = 275996979124493 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8416 = (513:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8416
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8417) ≤ val WuPaper.ClassicalFourthData.Bq 8417
    have hp : val WuPaper.ClassicalFourthData.Bq 8417 = (275999790539264:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8417 = 275999790539264 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8417 = (16417:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8417
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8418) ≤ val WuPaper.ClassicalFourthData.Bq 8418
    have hp : val WuPaper.ClassicalFourthData.Bq 8418 = (276002600031376:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8418 = 276002600031376 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8418 = (8209:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8418
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8419) ≤ val WuPaper.ClassicalFourthData.Bq 8419
    have hp : val WuPaper.ClassicalFourthData.Bq 8419 = (276005407601434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8419 = 276005407601434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8419 = (16419:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8419
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8420) ≤ val WuPaper.ClassicalFourthData.Bq 8420
    have hp : val WuPaper.ClassicalFourthData.Bq 8420 = (276008213250045:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8420 = 276008213250045 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8420 = (821:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8420
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8421) ≤ val WuPaper.ClassicalFourthData.Bq 8421
    have hp : val WuPaper.ClassicalFourthData.Bq 8421 = (276011016977814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8421 = 276011016977814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8421 = (16421:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8421
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8422) ≤ val WuPaper.ClassicalFourthData.Bq 8422
    have hp : val WuPaper.ClassicalFourthData.Bq 8422 = (276013818785346:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8422 = 276013818785346 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8422 = (8211:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8422
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8423) ≤ val WuPaper.ClassicalFourthData.Bq 8423
    have hp : val WuPaper.ClassicalFourthData.Bq 8423 = (276016618673246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8423 = 276016618673246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8423 = (16423:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8423
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8424) ≤ val WuPaper.ClassicalFourthData.Bq 8424
    have hp : val WuPaper.ClassicalFourthData.Bq 8424 = (276019416642118:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8424 = 276019416642118 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8424 = (2053:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8424
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8425) ≤ val WuPaper.ClassicalFourthData.Bq 8425
    have hp : val WuPaper.ClassicalFourthData.Bq 8425 = (276022212692568:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8425 = 276022212692568 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8425 = (657:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8425
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8426) ≤ val WuPaper.ClassicalFourthData.Bq 8426
    have hp : val WuPaper.ClassicalFourthData.Bq 8426 = (276025006825198:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8426 = 276025006825198 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8426 = (8213:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8426
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8427) ≤ val WuPaper.ClassicalFourthData.Bq 8427
    have hp : val WuPaper.ClassicalFourthData.Bq 8427 = (276027799040615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8427 = 276027799040615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8427 = (16427:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8427
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8428) ≤ val WuPaper.ClassicalFourthData.Bq 8428
    have hp : val WuPaper.ClassicalFourthData.Bq 8428 = (276030589339420:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8428 = 276030589339420 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8428 = (4107:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8428
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8429) ≤ val WuPaper.ClassicalFourthData.Bq 8429
    have hp : val WuPaper.ClassicalFourthData.Bq 8429 = (276033377722219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8429 = 276033377722219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8429 = (16429:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8429
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8430) ≤ val WuPaper.ClassicalFourthData.Bq 8430
    have hp : val WuPaper.ClassicalFourthData.Bq 8430 = (276036164189615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8430 = 276036164189615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8430 = (1643:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8430
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8431) ≤ val WuPaper.ClassicalFourthData.Bq 8431
    have hp : val WuPaper.ClassicalFourthData.Bq 8431 = (276038948742210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8431 = 276038948742210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8431 = (16431:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8431
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_526
