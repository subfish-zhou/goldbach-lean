import WR2ClassicalCPayments
import WR2ClassicalCPoints155
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_155 (j : Fin 16) : cPayment (16*155+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*155+j.val)+point (1327/200) 4096 (16*155+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2480 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2480+point (1327/200) 4096 2481)/2)
    have hp : cPayment 2480 = (54081994888:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2480+point (1327/200) 4096 2481)/2 = (5891247:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2480
  · change cPayment 2481 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2481+point (1327/200) 4096 2482)/2)
    have hp : cPayment 2481 = (54049234143:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2481+point (1327/200) 4096 2482)/2 = (5892301:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2481
  · change cPayment 2482 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2482+point (1327/200) 4096 2483)/2)
    have hp : cPayment 2482 = (54016467553:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2482+point (1327/200) 4096 2483)/2 = (1178671:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2482
  · change cPayment 2483 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2483+point (1327/200) 4096 2484)/2)
    have hp : cPayment 2483 = (53983695133:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2483+point (1327/200) 4096 2484)/2 = (5894409:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2483
  · change cPayment 2484 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2484+point (1327/200) 4096 2485)/2)
    have hp : cPayment 2484 = (53950916897:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2484+point (1327/200) 4096 2485)/2 = (5895463:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2484
  · change cPayment 2485 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2485+point (1327/200) 4096 2486)/2)
    have hp : cPayment 2485 = (53918132861:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2485+point (1327/200) 4096 2486)/2 = (5896517:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2485
  · change cPayment 2486 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2486+point (1327/200) 4096 2487)/2)
    have hp : cPayment 2486 = (53885343039:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2486+point (1327/200) 4096 2487)/2 = (5897571:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2486
  · change cPayment 2487 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2487+point (1327/200) 4096 2488)/2)
    have hp : cPayment 2487 = (53852547444:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2487+point (1327/200) 4096 2488)/2 = (235945:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2487
  · change cPayment 2488 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2488+point (1327/200) 4096 2489)/2)
    have hp : cPayment 2488 = (53819746093:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2488+point (1327/200) 4096 2489)/2 = (5899679:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2488
  · change cPayment 2489 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2489+point (1327/200) 4096 2490)/2)
    have hp : cPayment 2489 = (53786938999:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2489+point (1327/200) 4096 2490)/2 = (5900733:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2489
  · change cPayment 2490 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2490+point (1327/200) 4096 2491)/2)
    have hp : cPayment 2490 = (53754126177:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2490+point (1327/200) 4096 2491)/2 = (5901787:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2490
  · change cPayment 2491 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2491+point (1327/200) 4096 2492)/2)
    have hp : cPayment 2491 = (53721307640:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2491+point (1327/200) 4096 2492)/2 = (5902841:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2491
  · change cPayment 2492 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2492+point (1327/200) 4096 2493)/2)
    have hp : cPayment 2492 = (53688483405:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2492+point (1327/200) 4096 2493)/2 = (1180779:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2492
  · change cPayment 2493 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2493+point (1327/200) 4096 2494)/2)
    have hp : cPayment 2493 = (53655653484:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2493+point (1327/200) 4096 2494)/2 = (5904949:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2493
  · change cPayment 2494 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2494+point (1327/200) 4096 2495)/2)
    have hp : cPayment 2494 = (53622817894:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2494+point (1327/200) 4096 2495)/2 = (5906003:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2494
  · change cPayment 2495 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2495+point (1327/200) 4096 2496)/2)
    have hp : cPayment 2495 = (53589976646:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2495+point (1327/200) 4096 2496)/2 = (5907057:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2495
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_155
