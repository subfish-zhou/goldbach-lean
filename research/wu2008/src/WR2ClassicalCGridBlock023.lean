import WR2ClassicalCPayments
import WR2ClassicalCPoints023
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_023 (j : Fin 16) : cPayment (16*23+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*23+j.val)+point (1327/200) 4096 (16*23+j.val+1))/2) := by
  fin_cases j
  · change cPayment 368 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 368+point (1327/200) 4096 369)/2)
    have hp : cPayment 368 = (52715242014:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 368+point (1327/200) 4096 369)/2 = (3665199:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_368
  · change cPayment 369 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 369+point (1327/200) 4096 370)/2)
    have hp : cPayment 369 = (52809939929:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 369+point (1327/200) 4096 370)/2 = (3666253:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_369
  · change cPayment 370 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 370+point (1327/200) 4096 371)/2)
    have hp : cPayment 370 = (52904428017:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 370+point (1327/200) 4096 371)/2 = (3667307:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_370
  · change cPayment 371 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 371+point (1327/200) 4096 372)/2)
    have hp : cPayment 371 = (52998706625:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 371+point (1327/200) 4096 372)/2 = (3668361:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_371
  · change cPayment 372 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 372+point (1327/200) 4096 373)/2)
    have hp : cPayment 372 = (53092776100:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 372+point (1327/200) 4096 373)/2 = (733883:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_372
  · change cPayment 373 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 373+point (1327/200) 4096 374)/2)
    have hp : cPayment 373 = (53186636790:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 373+point (1327/200) 4096 374)/2 = (3670469:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_373
  · change cPayment 374 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 374+point (1327/200) 4096 375)/2)
    have hp : cPayment 374 = (53280289040:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 374+point (1327/200) 4096 375)/2 = (3671523:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_374
  · change cPayment 375 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 375+point (1327/200) 4096 376)/2)
    have hp : cPayment 375 = (53373733197:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 375+point (1327/200) 4096 376)/2 = (3672577:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_375
  · change cPayment 376 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 376+point (1327/200) 4096 377)/2)
    have hp : cPayment 376 = (53466969605:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 376+point (1327/200) 4096 377)/2 = (3673631:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_376
  · change cPayment 377 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 377+point (1327/200) 4096 378)/2)
    have hp : cPayment 377 = (53559998609:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 377+point (1327/200) 4096 378)/2 = (734937:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_377
  · change cPayment 378 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 378+point (1327/200) 4096 379)/2)
    have hp : cPayment 378 = (53652820552:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 378+point (1327/200) 4096 379)/2 = (3675739:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_378
  · change cPayment 379 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 379+point (1327/200) 4096 380)/2)
    have hp : cPayment 379 = (53745435777:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 379+point (1327/200) 4096 380)/2 = (3676793:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_379
  · change cPayment 380 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 380+point (1327/200) 4096 381)/2)
    have hp : cPayment 380 = (53837844627:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 380+point (1327/200) 4096 381)/2 = (3677847:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_380
  · change cPayment 381 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 381+point (1327/200) 4096 382)/2)
    have hp : cPayment 381 = (53930047443:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 381+point (1327/200) 4096 382)/2 = (3678901:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_381
  · change cPayment 382 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 382+point (1327/200) 4096 383)/2)
    have hp : cPayment 382 = (54022044566:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 382+point (1327/200) 4096 383)/2 = (735991:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_382
  · change cPayment 383 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 383+point (1327/200) 4096 384)/2)
    have hp : cPayment 383 = (54113836337:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 383+point (1327/200) 4096 384)/2 = (3681009:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_383
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_023
