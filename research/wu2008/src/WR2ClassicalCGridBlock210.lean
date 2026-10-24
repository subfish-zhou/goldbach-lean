import WR2ClassicalCPayments
import WR2ClassicalCPoints210
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_210 (j : Fin 16) : cPayment (16*210+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*210+j.val)+point (1327/200) 4096 (16*210+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3360 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3360+point (1327/200) 4096 3361)/2)
    have hp : cPayment 3360 = (24258441745:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3360+point (1327/200) 4096 3361)/2 = (6818767:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3360
  · change cPayment 3361 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3361+point (1327/200) 4096 3362)/2)
    have hp : cPayment 3361 = (24224508654:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3361+point (1327/200) 4096 3362)/2 = (6819821:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3361
  · change cPayment 3362 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3362+point (1327/200) 4096 3363)/2)
    have hp : cPayment 3362 = (24190577296:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3362+point (1327/200) 4096 3363)/2 = (272835:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3362
  · change cPayment 3363 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3363+point (1327/200) 4096 3364)/2)
    have hp : cPayment 3363 = (24156647676:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3363+point (1327/200) 4096 3364)/2 = (6821929:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3363
  · change cPayment 3364 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3364+point (1327/200) 4096 3365)/2)
    have hp : cPayment 3364 = (24122719799:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3364+point (1327/200) 4096 3365)/2 = (6822983:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3364
  · change cPayment 3365 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3365+point (1327/200) 4096 3366)/2)
    have hp : cPayment 3365 = (24088793669:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3365+point (1327/200) 4096 3366)/2 = (6824037:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3365
  · change cPayment 3366 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3366+point (1327/200) 4096 3367)/2)
    have hp : cPayment 3366 = (24054869290:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3366+point (1327/200) 4096 3367)/2 = (6825091:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3366
  · change cPayment 3367 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3367+point (1327/200) 4096 3368)/2)
    have hp : cPayment 3367 = (24020946666:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3367+point (1327/200) 4096 3368)/2 = (1365229:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3367
  · change cPayment 3368 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3368+point (1327/200) 4096 3369)/2)
    have hp : cPayment 3368 = (23987025803:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3368+point (1327/200) 4096 3369)/2 = (6827199:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3368
  · change cPayment 3369 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3369+point (1327/200) 4096 3370)/2)
    have hp : cPayment 3369 = (23953106704:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3369+point (1327/200) 4096 3370)/2 = (6828253:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3369
  · change cPayment 3370 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3370+point (1327/200) 4096 3371)/2)
    have hp : cPayment 3370 = (23919189375:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3370+point (1327/200) 4096 3371)/2 = (6829307:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3370
  · change cPayment 3371 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3371+point (1327/200) 4096 3372)/2)
    have hp : cPayment 3371 = (23885273819:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3371+point (1327/200) 4096 3372)/2 = (6830361:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3371
  · change cPayment 3372 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3372+point (1327/200) 4096 3373)/2)
    have hp : cPayment 3372 = (23851360040:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3372+point (1327/200) 4096 3373)/2 = (1366283:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3372
  · change cPayment 3373 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3373+point (1327/200) 4096 3374)/2)
    have hp : cPayment 3373 = (23817448044:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3373+point (1327/200) 4096 3374)/2 = (6832469:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3373
  · change cPayment 3374 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3374+point (1327/200) 4096 3375)/2)
    have hp : cPayment 3374 = (23783537835:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3374+point (1327/200) 4096 3375)/2 = (6833523:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3374
  · change cPayment 3375 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3375+point (1327/200) 4096 3376)/2)
    have hp : cPayment 3375 = (23749629417:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3375+point (1327/200) 4096 3376)/2 = (6834577:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3375
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_210
