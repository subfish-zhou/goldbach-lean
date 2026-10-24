import WR2ClassicalCPayments
import WR2ClassicalCPoints209
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_209 (j : Fin 16) : cPayment (16*209+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*209+j.val)+point (1327/200) 4096 (16*209+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3344 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3344+point (1327/200) 4096 3345)/2)
    have hp : cPayment 3344 = (24801603279:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3344+point (1327/200) 4096 3345)/2 = (6801903:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3344
  · change cPayment 3345 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3345+point (1327/200) 4096 3346)/2)
    have hp : cPayment 3345 = (24767643066:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3345+point (1327/200) 4096 3346)/2 = (6802957:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3345
  · change cPayment 3346 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3346+point (1327/200) 4096 3347)/2)
    have hp : cPayment 3346 = (24733684513:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3346+point (1327/200) 4096 3347)/2 = (6804011:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3346
  · change cPayment 3347 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3347+point (1327/200) 4096 3348)/2)
    have hp : cPayment 3347 = (24699727627:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3347+point (1327/200) 4096 3348)/2 = (1361013:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3347
  · change cPayment 3348 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3348+point (1327/200) 4096 3349)/2)
    have hp : cPayment 3348 = (24665772411:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3348+point (1327/200) 4096 3349)/2 = (6806119:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3348
  · change cPayment 3349 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3349+point (1327/200) 4096 3350)/2)
    have hp : cPayment 3349 = (24631818869:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3349+point (1327/200) 4096 3350)/2 = (6807173:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3349
  · change cPayment 3350 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3350+point (1327/200) 4096 3351)/2)
    have hp : cPayment 3350 = (24597867007:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3350+point (1327/200) 4096 3351)/2 = (6808227:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3350
  · change cPayment 3351 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3351+point (1327/200) 4096 3352)/2)
    have hp : cPayment 3351 = (24563916829:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3351+point (1327/200) 4096 3352)/2 = (6809281:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3351
  · change cPayment 3352 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3352+point (1327/200) 4096 3353)/2)
    have hp : cPayment 3352 = (24529968339:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3352+point (1327/200) 4096 3353)/2 = (1362067:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3352
  · change cPayment 3353 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3353+point (1327/200) 4096 3354)/2)
    have hp : cPayment 3353 = (24496021542:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3353+point (1327/200) 4096 3354)/2 = (6811389:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3353
  · change cPayment 3354 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3354+point (1327/200) 4096 3355)/2)
    have hp : cPayment 3354 = (24462076442:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3354+point (1327/200) 4096 3355)/2 = (6812443:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3354
  · change cPayment 3355 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3355+point (1327/200) 4096 3356)/2)
    have hp : cPayment 3355 = (24428133045:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3355+point (1327/200) 4096 3356)/2 = (6813497:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3355
  · change cPayment 3356 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3356+point (1327/200) 4096 3357)/2)
    have hp : cPayment 3356 = (24394191354:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3356+point (1327/200) 4096 3357)/2 = (6814551:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3356
  · change cPayment 3357 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3357+point (1327/200) 4096 3358)/2)
    have hp : cPayment 3357 = (24360251374:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3357+point (1327/200) 4096 3358)/2 = (1363121:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3357
  · change cPayment 3358 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3358+point (1327/200) 4096 3359)/2)
    have hp : cPayment 3358 = (24326313109:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3358+point (1327/200) 4096 3359)/2 = (6816659:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3358
  · change cPayment 3359 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3359+point (1327/200) 4096 3360)/2)
    have hp : cPayment 3359 = (24292376565:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3359+point (1327/200) 4096 3360)/2 = (6817713:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3359
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_209
