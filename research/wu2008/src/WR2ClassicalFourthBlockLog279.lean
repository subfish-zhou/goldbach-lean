import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints279
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_279 (j : Fin 16) (hj : 16*279+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*279+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*279+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4464) ≤ val WuPaper.ClassicalFourthData.Bq 4464
    have hp : val WuPaper.ClassicalFourthData.Bq 4464 = (240541564183586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4464 = 240541564183586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4464 = (779:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4464
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4465) ≤ val WuPaper.ClassicalFourthData.Bq 4465
    have hp : val WuPaper.ClassicalFourthData.Bq 4465 = (240560177927063:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4465 = 240560177927063 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4465 = (2493:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4465
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4466) ≤ val WuPaper.ClassicalFourthData.Bq 4466
    have hp : val WuPaper.ClassicalFourthData.Bq 4466 = (240578784206271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4466 = 240578784206271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4466 = (6233:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4466
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4467) ≤ val WuPaper.ClassicalFourthData.Bq 4467
    have hp : val WuPaper.ClassicalFourthData.Bq 4467 = (240597383024064:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4467 = 240597383024064 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4467 = (12467:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4467
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4468) ≤ val WuPaper.ClassicalFourthData.Bq 4468
    have hp : val WuPaper.ClassicalFourthData.Bq 4468 = (240615974383295:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4468 = 240615974383295 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4468 = (3117:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4468
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4469) ≤ val WuPaper.ClassicalFourthData.Bq 4469
    have hp : val WuPaper.ClassicalFourthData.Bq 4469 = (240634558286815:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4469 = 240634558286815 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4469 = (12469:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4469
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4470) ≤ val WuPaper.ClassicalFourthData.Bq 4470
    have hp : val WuPaper.ClassicalFourthData.Bq 4470 = (240653134737474:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4470 = 240653134737474 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4470 = (1247:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4470
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4471) ≤ val WuPaper.ClassicalFourthData.Bq 4471
    have hp : val WuPaper.ClassicalFourthData.Bq 4471 = (240671703738120:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4471 = 240671703738120 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4471 = (12471:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4471
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4472) ≤ val WuPaper.ClassicalFourthData.Bq 4472
    have hp : val WuPaper.ClassicalFourthData.Bq 4472 = (240690265291602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4472 = 240690265291602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4472 = (1559:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4472
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4473) ≤ val WuPaper.ClassicalFourthData.Bq 4473
    have hp : val WuPaper.ClassicalFourthData.Bq 4473 = (240708819400766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4473 = 240708819400766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4473 = (12473:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4473
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4474) ≤ val WuPaper.ClassicalFourthData.Bq 4474
    have hp : val WuPaper.ClassicalFourthData.Bq 4474 = (240727366068456:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4474 = 240727366068456 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4474 = (6237:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4474
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4475) ≤ val WuPaper.ClassicalFourthData.Bq 4475
    have hp : val WuPaper.ClassicalFourthData.Bq 4475 = (240745905297515:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4475 = 240745905297515 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4475 = (499:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4475
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4476) ≤ val WuPaper.ClassicalFourthData.Bq 4476
    have hp : val WuPaper.ClassicalFourthData.Bq 4476 = (240764437090787:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4476 = 240764437090787 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4476 = (3119:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4476
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4477) ≤ val WuPaper.ClassicalFourthData.Bq 4477
    have hp : val WuPaper.ClassicalFourthData.Bq 4477 = (240782961451111:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4477 = 240782961451111 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4477 = (12477:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4477
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4478) ≤ val WuPaper.ClassicalFourthData.Bq 4478
    have hp : val WuPaper.ClassicalFourthData.Bq 4478 = (240801478381329:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4478 = 240801478381329 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4478 = (6239:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4478
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4479) ≤ val WuPaper.ClassicalFourthData.Bq 4479
    have hp : val WuPaper.ClassicalFourthData.Bq 4479 = (240819987884278:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4479 = 240819987884278 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4479 = (12479:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4479
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_279
