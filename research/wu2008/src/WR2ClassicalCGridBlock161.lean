import WR2ClassicalCPayments
import WR2ClassicalCPoints161
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_161 (j : Fin 16) : cPayment (16*161+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*161+j.val)+point (1327/200) 4096 (16*161+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2576 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2576+point (1327/200) 4096 2577)/2)
    have hp : cPayment 2576 = (50912336919:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2576+point (1327/200) 4096 2577)/2 = (5992431:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2576
  · change cPayment 2577 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2577+point (1327/200) 4096 2578)/2)
    have hp : cPayment 2577 = (50879079039:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2577+point (1327/200) 4096 2578)/2 = (1198697:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2577
  · change cPayment 2578 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2578+point (1327/200) 4096 2579)/2)
    have hp : cPayment 2578 = (50845816632:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2578+point (1327/200) 4096 2579)/2 = (5994539:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2578
  · change cPayment 2579 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2579+point (1327/200) 4096 2580)/2)
    have hp : cPayment 2579 = (50812549712:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2579+point (1327/200) 4096 2580)/2 = (5995593:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2579
  · change cPayment 2580 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2580+point (1327/200) 4096 2581)/2)
    have hp : cPayment 2580 = (50779278292:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2580+point (1327/200) 4096 2581)/2 = (5996647:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2580
  · change cPayment 2581 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2581+point (1327/200) 4096 2582)/2)
    have hp : cPayment 2581 = (50746002383:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2581+point (1327/200) 4096 2582)/2 = (5997701:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2581
  · change cPayment 2582 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2582+point (1327/200) 4096 2583)/2)
    have hp : cPayment 2582 = (50712721999:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2582+point (1327/200) 4096 2583)/2 = (1199751:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2582
  · change cPayment 2583 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2583+point (1327/200) 4096 2584)/2)
    have hp : cPayment 2583 = (50679437152:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2583+point (1327/200) 4096 2584)/2 = (5999809:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2583
  · change cPayment 2584 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2584+point (1327/200) 4096 2585)/2)
    have hp : cPayment 2584 = (50646147856:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2584+point (1327/200) 4096 2585)/2 = (6000863:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2584
  · change cPayment 2585 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2585+point (1327/200) 4096 2586)/2)
    have hp : cPayment 2585 = (50612854123:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2585+point (1327/200) 4096 2586)/2 = (6001917:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2585
  · change cPayment 2586 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2586+point (1327/200) 4096 2587)/2)
    have hp : cPayment 2586 = (50579555966:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2586+point (1327/200) 4096 2587)/2 = (6002971:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2586
  · change cPayment 2587 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2587+point (1327/200) 4096 2588)/2)
    have hp : cPayment 2587 = (50546253397:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2587+point (1327/200) 4096 2588)/2 = (240161:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2587
  · change cPayment 2588 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2588+point (1327/200) 4096 2589)/2)
    have hp : cPayment 2588 = (50512946430:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2588+point (1327/200) 4096 2589)/2 = (6005079:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2588
  · change cPayment 2589 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2589+point (1327/200) 4096 2590)/2)
    have hp : cPayment 2589 = (50479635077:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2589+point (1327/200) 4096 2590)/2 = (6006133:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2589
  · change cPayment 2590 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2590+point (1327/200) 4096 2591)/2)
    have hp : cPayment 2590 = (50446319350:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2590+point (1327/200) 4096 2591)/2 = (6007187:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2590
  · change cPayment 2591 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2591+point (1327/200) 4096 2592)/2)
    have hp : cPayment 2591 = (50412999263:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2591+point (1327/200) 4096 2592)/2 = (6008241:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2591
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_161
