import WR2ClassicalCPayments
import WR2ClassicalCPoints163
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_163 (j : Fin 16) : cPayment (16*163+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*163+j.val)+point (1327/200) 4096 (16*163+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2608 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2608+point (1327/200) 4096 2609)/2)
    have hp : cPayment 2608 = (49845902797:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2608+point (1327/200) 4096 2609)/2 = (6026159:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2608
  · change cPayment 2609 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2609+point (1327/200) 4096 2610)/2)
    have hp : cPayment 2609 = (49812506365:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2609+point (1327/200) 4096 2610)/2 = (6027213:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2609
  · change cPayment 2610 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2610+point (1327/200) 4096 2611)/2)
    have hp : cPayment 2610 = (49779105810:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2610+point (1327/200) 4096 2611)/2 = (6028267:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2610
  · change cPayment 2611 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2611+point (1327/200) 4096 2612)/2)
    have hp : cPayment 2611 = (49745701144:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2611+point (1327/200) 4096 2612)/2 = (6029321:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2611
  · change cPayment 2612 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2612+point (1327/200) 4096 2613)/2)
    have hp : cPayment 2612 = (49712292380:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2612+point (1327/200) 4096 2613)/2 = (241215:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2612
  · change cPayment 2613 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2613+point (1327/200) 4096 2614)/2)
    have hp : cPayment 2613 = (49678879529:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2613+point (1327/200) 4096 2614)/2 = (6031429:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2613
  · change cPayment 2614 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2614+point (1327/200) 4096 2615)/2)
    have hp : cPayment 2614 = (49645462604:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2614+point (1327/200) 4096 2615)/2 = (6032483:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2614
  · change cPayment 2615 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2615+point (1327/200) 4096 2616)/2)
    have hp : cPayment 2615 = (49612041618:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2615+point (1327/200) 4096 2616)/2 = (6033537:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2615
  · change cPayment 2616 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2616+point (1327/200) 4096 2617)/2)
    have hp : cPayment 2616 = (49578616582:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2616+point (1327/200) 4096 2617)/2 = (6034591:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2616
  · change cPayment 2617 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2617+point (1327/200) 4096 2618)/2)
    have hp : cPayment 2617 = (49545187509:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2617+point (1327/200) 4096 2618)/2 = (1207129:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2617
  · change cPayment 2618 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2618+point (1327/200) 4096 2619)/2)
    have hp : cPayment 2618 = (49511754411:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2618+point (1327/200) 4096 2619)/2 = (6036699:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2618
  · change cPayment 2619 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2619+point (1327/200) 4096 2620)/2)
    have hp : cPayment 2619 = (49478317300:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2619+point (1327/200) 4096 2620)/2 = (6037753:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2619
  · change cPayment 2620 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2620+point (1327/200) 4096 2621)/2)
    have hp : cPayment 2620 = (49444876189:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2620+point (1327/200) 4096 2621)/2 = (6038807:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2620
  · change cPayment 2621 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2621+point (1327/200) 4096 2622)/2)
    have hp : cPayment 2621 = (49411431089:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2621+point (1327/200) 4096 2622)/2 = (6039861:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2621
  · change cPayment 2622 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2622+point (1327/200) 4096 2623)/2)
    have hp : cPayment 2622 = (49377982013:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2622+point (1327/200) 4096 2623)/2 = (1208183:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2622
  · change cPayment 2623 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2623+point (1327/200) 4096 2624)/2)
    have hp : cPayment 2623 = (49344528973:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2623+point (1327/200) 4096 2624)/2 = (6041969:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2623
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_163
