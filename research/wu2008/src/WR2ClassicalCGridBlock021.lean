import WR2ClassicalCPayments
import WR2ClassicalCPoints021
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_021 (j : Fin 16) : cPayment (16*21+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*21+j.val)+point (1327/200) 4096 (16*21+j.val+1))/2) := by
  fin_cases j
  · change cPayment 336 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 336+point (1327/200) 4096 337)/2)
    have hp : cPayment 336 = (49572001549:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 336+point (1327/200) 4096 337)/2 = (3631471:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_336
  · change cPayment 337 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 337+point (1327/200) 4096 338)/2)
    have hp : cPayment 337 = (49673601756:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 337+point (1327/200) 4096 338)/2 = (145301:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_337
  · change cPayment 338 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 338+point (1327/200) 4096 339)/2)
    have hp : cPayment 338 = (49774980641:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 338+point (1327/200) 4096 339)/2 = (3633579:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_338
  · change cPayment 339 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 339+point (1327/200) 4096 340)/2)
    have hp : cPayment 339 = (49876138576:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 339+point (1327/200) 4096 340)/2 = (3634633:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_339
  · change cPayment 340 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 340+point (1327/200) 4096 341)/2)
    have hp : cPayment 340 = (49977075928:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 340+point (1327/200) 4096 341)/2 = (3635687:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_340
  · change cPayment 341 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 341+point (1327/200) 4096 342)/2)
    have hp : cPayment 341 = (50077793066:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 341+point (1327/200) 4096 342)/2 = (3636741:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_341
  · change cPayment 342 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 342+point (1327/200) 4096 343)/2)
    have hp : cPayment 342 = (50178290358:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 342+point (1327/200) 4096 343)/2 = (727559:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_342
  · change cPayment 343 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 343+point (1327/200) 4096 344)/2)
    have hp : cPayment 343 = (50278568170:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 343+point (1327/200) 4096 344)/2 = (3638849:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_343
  · change cPayment 344 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 344+point (1327/200) 4096 345)/2)
    have hp : cPayment 344 = (50378626869:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 344+point (1327/200) 4096 345)/2 = (3639903:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_344
  · change cPayment 345 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 345+point (1327/200) 4096 346)/2)
    have hp : cPayment 345 = (50478466821:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 345+point (1327/200) 4096 346)/2 = (3640957:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_345
  · change cPayment 346 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 346+point (1327/200) 4096 347)/2)
    have hp : cPayment 346 = (50578088390:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 346+point (1327/200) 4096 347)/2 = (3642011:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_346
  · change cPayment 347 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 347+point (1327/200) 4096 348)/2)
    have hp : cPayment 347 = (50677491941:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 347+point (1327/200) 4096 348)/2 = (728613:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_347
  · change cPayment 348 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 348+point (1327/200) 4096 349)/2)
    have hp : cPayment 348 = (50776677836:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 348+point (1327/200) 4096 349)/2 = (3644119:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_348
  · change cPayment 349 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 349+point (1327/200) 4096 350)/2)
    have hp : cPayment 349 = (50875646440:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 349+point (1327/200) 4096 350)/2 = (3645173:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_349
  · change cPayment 350 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 350+point (1327/200) 4096 351)/2)
    have hp : cPayment 350 = (50974398113:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 350+point (1327/200) 4096 351)/2 = (3646227:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_350
  · change cPayment 351 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 351+point (1327/200) 4096 352)/2)
    have hp : cPayment 351 = (51072933218:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 351+point (1327/200) 4096 352)/2 = (3647281:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_351
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_021
