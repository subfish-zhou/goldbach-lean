import WR2ClassicalCPayments
import WR2ClassicalCPoints022
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_022 (j : Fin 16) : cPayment (16*22+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*22+j.val)+point (1327/200) 4096 (16*22+j.val+1))/2) := by
  fin_cases j
  · change cPayment 352 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 352+point (1327/200) 4096 353)/2)
    have hp : cPayment 352 = (51171252116:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 352+point (1327/200) 4096 353)/2 = (729667:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_352
  · change cPayment 353 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 353+point (1327/200) 4096 354)/2)
    have hp : cPayment 353 = (51269355165:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 353+point (1327/200) 4096 354)/2 = (3649389:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_353
  · change cPayment 354 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 354+point (1327/200) 4096 355)/2)
    have hp : cPayment 354 = (51367242727:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 354+point (1327/200) 4096 355)/2 = (3650443:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_354
  · change cPayment 355 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 355+point (1327/200) 4096 356)/2)
    have hp : cPayment 355 = (51464915159:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 355+point (1327/200) 4096 356)/2 = (3651497:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_355
  · change cPayment 356 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 356+point (1327/200) 4096 357)/2)
    have hp : cPayment 356 = (51562372819:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 356+point (1327/200) 4096 357)/2 = (3652551:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_356
  · change cPayment 357 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 357+point (1327/200) 4096 358)/2)
    have hp : cPayment 357 = (51659616066:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 357+point (1327/200) 4096 358)/2 = (730721:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_357
  · change cPayment 358 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 358+point (1327/200) 4096 359)/2)
    have hp : cPayment 358 = (51756645256:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 358+point (1327/200) 4096 359)/2 = (3654659:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_358
  · change cPayment 359 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 359+point (1327/200) 4096 360)/2)
    have hp : cPayment 359 = (51853460744:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 359+point (1327/200) 4096 360)/2 = (3655713:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_359
  · change cPayment 360 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 360+point (1327/200) 4096 361)/2)
    have hp : cPayment 360 = (51950062887:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 360+point (1327/200) 4096 361)/2 = (3656767:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_360
  · change cPayment 361 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 361+point (1327/200) 4096 362)/2)
    have hp : cPayment 361 = (52046452039:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 361+point (1327/200) 4096 362)/2 = (3657821:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_361
  · change cPayment 362 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 362+point (1327/200) 4096 363)/2)
    have hp : cPayment 362 = (52142628554:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 362+point (1327/200) 4096 363)/2 = (146355:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_362
  · change cPayment 363 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 363+point (1327/200) 4096 364)/2)
    have hp : cPayment 363 = (52238592785:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 363+point (1327/200) 4096 364)/2 = (3659929:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_363
  · change cPayment 364 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 364+point (1327/200) 4096 365)/2)
    have hp : cPayment 364 = (52334345086:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 364+point (1327/200) 4096 365)/2 = (3660983:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_364
  · change cPayment 365 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 365+point (1327/200) 4096 366)/2)
    have hp : cPayment 365 = (52429885808:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 365+point (1327/200) 4096 366)/2 = (3662037:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_365
  · change cPayment 366 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 366+point (1327/200) 4096 367)/2)
    have hp : cPayment 366 = (52525215303:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 366+point (1327/200) 4096 367)/2 = (3663091:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_366
  · change cPayment 367 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 367+point (1327/200) 4096 368)/2)
    have hp : cPayment 367 = (52620333922:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 367+point (1327/200) 4096 368)/2 = (732829:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_367
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_022
