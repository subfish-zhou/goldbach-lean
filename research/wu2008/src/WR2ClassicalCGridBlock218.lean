import WR2ClassicalCPayments
import WR2ClassicalCPoints218
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_218 (j : Fin 16) : cPayment (16*218+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*218+j.val)+point (1327/200) 4096 (16*218+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3488 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3488+point (1327/200) 4096 3489)/2)
    have hp : cPayment 3488 = (19930556550:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3488+point (1327/200) 4096 3489)/2 = (6953679:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3488
  · change cPayment 3489 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3489+point (1327/200) 4096 3490)/2)
    have hp : cPayment 3489 = (19896879610:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3489+point (1327/200) 4096 3490)/2 = (6954733:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3489
  · change cPayment 3490 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3490+point (1327/200) 4096 3491)/2)
    have hp : cPayment 3490 = (19863204927:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3490+point (1327/200) 4096 3491)/2 = (6955787:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3490
  · change cPayment 3491 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3491+point (1327/200) 4096 3492)/2)
    have hp : cPayment 3491 = (19829532505:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3491+point (1327/200) 4096 3492)/2 = (6956841:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3491
  · change cPayment 3492 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3492+point (1327/200) 4096 3493)/2)
    have hp : cPayment 3492 = (19795862348:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3492+point (1327/200) 4096 3493)/2 = (1391579:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3492
  · change cPayment 3493 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3493+point (1327/200) 4096 3494)/2)
    have hp : cPayment 3493 = (19762194459:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3493+point (1327/200) 4096 3494)/2 = (6958949:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3493
  · change cPayment 3494 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3494+point (1327/200) 4096 3495)/2)
    have hp : cPayment 3494 = (19728528841:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3494+point (1327/200) 4096 3495)/2 = (6960003:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3494
  · change cPayment 3495 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3495+point (1327/200) 4096 3496)/2)
    have hp : cPayment 3495 = (19694865500:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3495+point (1327/200) 4096 3496)/2 = (6961057:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3495
  · change cPayment 3496 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3496+point (1327/200) 4096 3497)/2)
    have hp : cPayment 3496 = (19661204438:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3496+point (1327/200) 4096 3497)/2 = (6962111:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3496
  · change cPayment 3497 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3497+point (1327/200) 4096 3498)/2)
    have hp : cPayment 3497 = (19627545659:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3497+point (1327/200) 4096 3498)/2 = (1392633:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3497
  · change cPayment 3498 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3498+point (1327/200) 4096 3499)/2)
    have hp : cPayment 3498 = (19593889167:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3498+point (1327/200) 4096 3499)/2 = (6964219:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3498
  · change cPayment 3499 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3499+point (1327/200) 4096 3500)/2)
    have hp : cPayment 3499 = (19560234965:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3499+point (1327/200) 4096 3500)/2 = (6965273:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3499
  · change cPayment 3500 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3500+point (1327/200) 4096 3501)/2)
    have hp : cPayment 3500 = (19526583058:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3500+point (1327/200) 4096 3501)/2 = (6966327:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3500
  · change cPayment 3501 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3501+point (1327/200) 4096 3502)/2)
    have hp : cPayment 3501 = (19492933448:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3501+point (1327/200) 4096 3502)/2 = (6967381:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3501
  · change cPayment 3502 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3502+point (1327/200) 4096 3503)/2)
    have hp : cPayment 3502 = (19459286140:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3502+point (1327/200) 4096 3503)/2 = (1393687:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3502
  · change cPayment 3503 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3503+point (1327/200) 4096 3504)/2)
    have hp : cPayment 3503 = (19425641137:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3503+point (1327/200) 4096 3504)/2 = (6969489:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3503
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_218
