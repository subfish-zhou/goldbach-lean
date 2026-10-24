import WR2ClassicalCPayments
import WR2ClassicalCPoints029
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_029 (j : Fin 16) : cPayment (16*29+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*29+j.val)+point (1327/200) 4096 (16*29+j.val+1))/2) := by
  fin_cases j
  · change cPayment 464 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 464+point (1327/200) 4096 465)/2)
    have hp : cPayment 464 = (60897097423:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 464+point (1327/200) 4096 465)/2 = (3766383:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_464
  · change cPayment 465 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 465+point (1327/200) 4096 466)/2)
    have hp : cPayment 465 = (60973151170:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 465+point (1327/200) 4096 466)/2 = (3767437:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_465
  · change cPayment 466 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 466+point (1327/200) 4096 467)/2)
    have hp : cPayment 466 = (61049025742:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 466+point (1327/200) 4096 467)/2 = (3768491:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_466
  · change cPayment 467 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 467+point (1327/200) 4096 468)/2)
    have hp : cPayment 467 = (61124721431:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 467+point (1327/200) 4096 468)/2 = (753909:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_467
  · change cPayment 468 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 468+point (1327/200) 4096 469)/2)
    have hp : cPayment 468 = (61200238529:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 468+point (1327/200) 4096 469)/2 = (3770599:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_468
  · change cPayment 469 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 469+point (1327/200) 4096 470)/2)
    have hp : cPayment 469 = (61275577326:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 469+point (1327/200) 4096 470)/2 = (3771653:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_469
  · change cPayment 470 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 470+point (1327/200) 4096 471)/2)
    have hp : cPayment 470 = (61350738112:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 470+point (1327/200) 4096 471)/2 = (3772707:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_470
  · change cPayment 471 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 471+point (1327/200) 4096 472)/2)
    have hp : cPayment 471 = (61425721177:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 471+point (1327/200) 4096 472)/2 = (3773761:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_471
  · change cPayment 472 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 472+point (1327/200) 4096 473)/2)
    have hp : cPayment 472 = (61500526811:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 472+point (1327/200) 4096 473)/2 = (754963:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_472
  · change cPayment 473 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 473+point (1327/200) 4096 474)/2)
    have hp : cPayment 473 = (61575155301:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 473+point (1327/200) 4096 474)/2 = (3775869:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_473
  · change cPayment 474 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 474+point (1327/200) 4096 475)/2)
    have hp : cPayment 474 = (61649606937:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 474+point (1327/200) 4096 475)/2 = (3776923:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_474
  · change cPayment 475 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 475+point (1327/200) 4096 476)/2)
    have hp : cPayment 475 = (61723882005:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 475+point (1327/200) 4096 476)/2 = (3777977:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_475
  · change cPayment 476 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 476+point (1327/200) 4096 477)/2)
    have hp : cPayment 476 = (61797980793:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 476+point (1327/200) 4096 477)/2 = (3779031:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_476
  · change cPayment 477 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 477+point (1327/200) 4096 478)/2)
    have hp : cPayment 477 = (61871903587:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 477+point (1327/200) 4096 478)/2 = (756017:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_477
  · change cPayment 478 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 478+point (1327/200) 4096 479)/2)
    have hp : cPayment 478 = (61945650674:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 478+point (1327/200) 4096 479)/2 = (3781139:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_478
  · change cPayment 479 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 479+point (1327/200) 4096 480)/2)
    have hp : cPayment 479 = (62019222338:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 479+point (1327/200) 4096 480)/2 = (3782193:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_479
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_029
