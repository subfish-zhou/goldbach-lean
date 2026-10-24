import WR2ClassicalCPayments
import WR2ClassicalCPoints157
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_157 (j : Fin 16) : cPayment (16*157+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*157+j.val)+point (1327/200) 4096 (16*157+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2512 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2512+point (1327/200) 4096 2513)/2)
    have hp : cPayment 2512 = (53030823898:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2512+point (1327/200) 4096 2513)/2 = (236999:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2512
  · change cPayment 2513 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2513+point (1327/200) 4096 2514)/2)
    have hp : cPayment 2513 = (52997883278:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2513+point (1327/200) 4096 2514)/2 = (5926029:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2513
  · change cPayment 2514 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2514+point (1327/200) 4096 2515)/2)
    have hp : cPayment 2514 = (52964937271:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2514+point (1327/200) 4096 2515)/2 = (5927083:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2514
  · change cPayment 2515 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2515+point (1327/200) 4096 2516)/2)
    have hp : cPayment 2515 = (52931985892:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2515+point (1327/200) 4096 2516)/2 = (5928137:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2515
  · change cPayment 2516 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2516+point (1327/200) 4096 2517)/2)
    have hp : cPayment 2516 = (52899029154:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2516+point (1327/200) 4096 2517)/2 = (5929191:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2516
  · change cPayment 2517 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2517+point (1327/200) 4096 2518)/2)
    have hp : cPayment 2517 = (52866067072:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2517+point (1327/200) 4096 2518)/2 = (1186049:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2517
  · change cPayment 2518 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2518+point (1327/200) 4096 2519)/2)
    have hp : cPayment 2518 = (52833099659:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2518+point (1327/200) 4096 2519)/2 = (5931299:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2518
  · change cPayment 2519 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2519+point (1327/200) 4096 2520)/2)
    have hp : cPayment 2519 = (52800126930:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2519+point (1327/200) 4096 2520)/2 = (5932353:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2519
  · change cPayment 2520 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2520+point (1327/200) 4096 2521)/2)
    have hp : cPayment 2520 = (52767148897:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2520+point (1327/200) 4096 2521)/2 = (5933407:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2520
  · change cPayment 2521 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2521+point (1327/200) 4096 2522)/2)
    have hp : cPayment 2521 = (52734165576:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2521+point (1327/200) 4096 2522)/2 = (5934461:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2521
  · change cPayment 2522 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2522+point (1327/200) 4096 2523)/2)
    have hp : cPayment 2522 = (52701176980:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2522+point (1327/200) 4096 2523)/2 = (1187103:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2522
  · change cPayment 2523 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2523+point (1327/200) 4096 2524)/2)
    have hp : cPayment 2523 = (52668183123:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2523+point (1327/200) 4096 2524)/2 = (5936569:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2523
  · change cPayment 2524 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2524+point (1327/200) 4096 2525)/2)
    have hp : cPayment 2524 = (52635184018:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2524+point (1327/200) 4096 2525)/2 = (5937623:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2524
  · change cPayment 2525 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2525+point (1327/200) 4096 2526)/2)
    have hp : cPayment 2525 = (52602179680:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2525+point (1327/200) 4096 2526)/2 = (5938677:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2525
  · change cPayment 2526 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2526+point (1327/200) 4096 2527)/2)
    have hp : cPayment 2526 = (52569170123:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2526+point (1327/200) 4096 2527)/2 = (5939731:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2526
  · change cPayment 2527 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2527+point (1327/200) 4096 2528)/2)
    have hp : cPayment 2527 = (52536155359:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2527+point (1327/200) 4096 2528)/2 = (1188157:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2527
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_157
