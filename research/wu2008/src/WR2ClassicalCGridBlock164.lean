import WR2ClassicalCPayments
import WR2ClassicalCPoints164
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_164 (j : Fin 16) : cPayment (16*164+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*164+j.val)+point (1327/200) 4096 (16*164+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2624 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2624+point (1327/200) 4096 2625)/2)
    have hp : cPayment 2624 = (49311071981:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2624+point (1327/200) 4096 2625)/2 = (6043023:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2624
  · change cPayment 2625 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2625+point (1327/200) 4096 2626)/2)
    have hp : cPayment 2625 = (49277611049:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2625+point (1327/200) 4096 2626)/2 = (6044077:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2625
  · change cPayment 2626 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2626+point (1327/200) 4096 2627)/2)
    have hp : cPayment 2626 = (49244146189:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2626+point (1327/200) 4096 2627)/2 = (6045131:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2626
  · change cPayment 2627 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2627+point (1327/200) 4096 2628)/2)
    have hp : cPayment 2627 = (49210677413:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2627+point (1327/200) 4096 2628)/2 = (1209237:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2627
  · change cPayment 2628 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2628+point (1327/200) 4096 2629)/2)
    have hp : cPayment 2628 = (49177204734:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2628+point (1327/200) 4096 2629)/2 = (6047239:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2628
  · change cPayment 2629 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2629+point (1327/200) 4096 2630)/2)
    have hp : cPayment 2629 = (49143728163:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2629+point (1327/200) 4096 2630)/2 = (6048293:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2629
  · change cPayment 2630 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2630+point (1327/200) 4096 2631)/2)
    have hp : cPayment 2630 = (49110247713:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2630+point (1327/200) 4096 2631)/2 = (6049347:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2630
  · change cPayment 2631 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2631+point (1327/200) 4096 2632)/2)
    have hp : cPayment 2631 = (49076763395:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2631+point (1327/200) 4096 2632)/2 = (6050401:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2631
  · change cPayment 2632 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2632+point (1327/200) 4096 2633)/2)
    have hp : cPayment 2632 = (49043275221:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2632+point (1327/200) 4096 2633)/2 = (1210291:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2632
  · change cPayment 2633 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2633+point (1327/200) 4096 2634)/2)
    have hp : cPayment 2633 = (49009783204:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2633+point (1327/200) 4096 2634)/2 = (6052509:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2633
  · change cPayment 2634 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2634+point (1327/200) 4096 2635)/2)
    have hp : cPayment 2634 = (48976287355:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2634+point (1327/200) 4096 2635)/2 = (6053563:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2634
  · change cPayment 2635 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2635+point (1327/200) 4096 2636)/2)
    have hp : cPayment 2635 = (48942787686:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2635+point (1327/200) 4096 2636)/2 = (6054617:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2635
  · change cPayment 2636 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2636+point (1327/200) 4096 2637)/2)
    have hp : cPayment 2636 = (48909284209:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2636+point (1327/200) 4096 2637)/2 = (6055671:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2636
  · change cPayment 2637 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2637+point (1327/200) 4096 2638)/2)
    have hp : cPayment 2637 = (48875776937:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2637+point (1327/200) 4096 2638)/2 = (242269:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2637
  · change cPayment 2638 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2638+point (1327/200) 4096 2639)/2)
    have hp : cPayment 2638 = (48842265881:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2638+point (1327/200) 4096 2639)/2 = (6057779:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2638
  · change cPayment 2639 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2639+point (1327/200) 4096 2640)/2)
    have hp : cPayment 2639 = (48808751052:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2639+point (1327/200) 4096 2640)/2 = (6058833:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2639
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_164
