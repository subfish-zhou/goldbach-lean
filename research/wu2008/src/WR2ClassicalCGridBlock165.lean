import WR2ClassicalCPayments
import WR2ClassicalCPoints165
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_165 (j : Fin 16) : cPayment (16*165+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*165+j.val)+point (1327/200) 4096 (16*165+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2640 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2640+point (1327/200) 4096 2641)/2)
    have hp : cPayment 2640 = (48775232464:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2640+point (1327/200) 4096 2641)/2 = (6059887:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2640
  · change cPayment 2641 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2641+point (1327/200) 4096 2642)/2)
    have hp : cPayment 2641 = (48741710127:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2641+point (1327/200) 4096 2642)/2 = (6060941:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2641
  · change cPayment 2642 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2642+point (1327/200) 4096 2643)/2)
    have hp : cPayment 2642 = (48708184053:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2642+point (1327/200) 4096 2643)/2 = (1212399:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2642
  · change cPayment 2643 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2643+point (1327/200) 4096 2644)/2)
    have hp : cPayment 2643 = (48674654255:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2643+point (1327/200) 4096 2644)/2 = (6063049:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2643
  · change cPayment 2644 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2644+point (1327/200) 4096 2645)/2)
    have hp : cPayment 2644 = (48641120744:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2644+point (1327/200) 4096 2645)/2 = (6064103:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2644
  · change cPayment 2645 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2645+point (1327/200) 4096 2646)/2)
    have hp : cPayment 2645 = (48607583531:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2645+point (1327/200) 4096 2646)/2 = (6065157:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2645
  · change cPayment 2646 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2646+point (1327/200) 4096 2647)/2)
    have hp : cPayment 2646 = (48574042630:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2646+point (1327/200) 4096 2647)/2 = (6066211:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2646
  · change cPayment 2647 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2647+point (1327/200) 4096 2648)/2)
    have hp : cPayment 2647 = (48540498051:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2647+point (1327/200) 4096 2648)/2 = (1213453:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2647
  · change cPayment 2648 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2648+point (1327/200) 4096 2649)/2)
    have hp : cPayment 2648 = (48506949805:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2648+point (1327/200) 4096 2649)/2 = (6068319:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2648
  · change cPayment 2649 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2649+point (1327/200) 4096 2650)/2)
    have hp : cPayment 2649 = (48473397906:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2649+point (1327/200) 4096 2650)/2 = (6069373:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2649
  · change cPayment 2650 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2650+point (1327/200) 4096 2651)/2)
    have hp : cPayment 2650 = (48439842365:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2650+point (1327/200) 4096 2651)/2 = (6070427:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2650
  · change cPayment 2651 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2651+point (1327/200) 4096 2652)/2)
    have hp : cPayment 2651 = (48406283192:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2651+point (1327/200) 4096 2652)/2 = (6071481:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2651
  · change cPayment 2652 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2652+point (1327/200) 4096 2653)/2)
    have hp : cPayment 2652 = (48372720401:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2652+point (1327/200) 4096 2653)/2 = (1214507:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2652
  · change cPayment 2653 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2653+point (1327/200) 4096 2654)/2)
    have hp : cPayment 2653 = (48339154002:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2653+point (1327/200) 4096 2654)/2 = (6073589:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2653
  · change cPayment 2654 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2654+point (1327/200) 4096 2655)/2)
    have hp : cPayment 2654 = (48305584008:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2654+point (1327/200) 4096 2655)/2 = (6074643:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2654
  · change cPayment 2655 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2655+point (1327/200) 4096 2656)/2)
    have hp : cPayment 2655 = (48272010430:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2655+point (1327/200) 4096 2656)/2 = (6075697:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2655
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_165
