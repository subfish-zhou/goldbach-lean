import WR2ClassicalCPayments
import WR2ClassicalCPoints148
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_148 (j : Fin 16) : cPayment (16*148+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*148+j.val)+point (1327/200) 4096 (16*148+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2368 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2368+point (1327/200) 4096 2369)/2)
    have hp : cPayment 2368 = (57710562071:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2368+point (1327/200) 4096 2369)/2 = (5773199:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2368
  · change cPayment 2369 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2369+point (1327/200) 4096 2370)/2)
    have hp : cPayment 2369 = (57678553224:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2369+point (1327/200) 4096 2370)/2 = (5774253:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2369
  · change cPayment 2370 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2370+point (1327/200) 4096 2371)/2)
    have hp : cPayment 2370 = (57646536766:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2370+point (1327/200) 4096 2371)/2 = (5775307:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2370
  · change cPayment 2371 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2371+point (1327/200) 4096 2372)/2)
    have hp : cPayment 2371 = (57614512716:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2371+point (1327/200) 4096 2372)/2 = (5776361:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2371
  · change cPayment 2372 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2372+point (1327/200) 4096 2373)/2)
    have hp : cPayment 2372 = (57582481089:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2372+point (1327/200) 4096 2373)/2 = (1155483:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2372
  · change cPayment 2373 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2373+point (1327/200) 4096 2374)/2)
    have hp : cPayment 2373 = (57550441903:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2373+point (1327/200) 4096 2374)/2 = (5778469:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2373
  · change cPayment 2374 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2374+point (1327/200) 4096 2375)/2)
    have hp : cPayment 2374 = (57518395175:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2374+point (1327/200) 4096 2375)/2 = (5779523:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2374
  · change cPayment 2375 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2375+point (1327/200) 4096 2376)/2)
    have hp : cPayment 2375 = (57486340921:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2375+point (1327/200) 4096 2376)/2 = (5780577:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2375
  · change cPayment 2376 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2376+point (1327/200) 4096 2377)/2)
    have hp : cPayment 2376 = (57454279158:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2376+point (1327/200) 4096 2377)/2 = (5781631:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2376
  · change cPayment 2377 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2377+point (1327/200) 4096 2378)/2)
    have hp : cPayment 2377 = (57422209903:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2377+point (1327/200) 4096 2378)/2 = (1156537:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2377
  · change cPayment 2378 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2378+point (1327/200) 4096 2379)/2)
    have hp : cPayment 2378 = (57390133173:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2378+point (1327/200) 4096 2379)/2 = (5783739:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2378
  · change cPayment 2379 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2379+point (1327/200) 4096 2380)/2)
    have hp : cPayment 2379 = (57358048985:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2379+point (1327/200) 4096 2380)/2 = (5784793:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2379
  · change cPayment 2380 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2380+point (1327/200) 4096 2381)/2)
    have hp : cPayment 2380 = (57325957355:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2380+point (1327/200) 4096 2381)/2 = (5785847:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2380
  · change cPayment 2381 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2381+point (1327/200) 4096 2382)/2)
    have hp : cPayment 2381 = (57293858301:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2381+point (1327/200) 4096 2382)/2 = (5786901:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2381
  · change cPayment 2382 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2382+point (1327/200) 4096 2383)/2)
    have hp : cPayment 2382 = (57261751838:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2382+point (1327/200) 4096 2383)/2 = (1157591:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2382
  · change cPayment 2383 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2383+point (1327/200) 4096 2384)/2)
    have hp : cPayment 2383 = (57229637984:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2383+point (1327/200) 4096 2384)/2 = (5789009:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2383
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_148
