import WR2ClassicalCPayments
import WR2ClassicalCPoints031
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_031 (j : Fin 16) : cPayment (16*31+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*31+j.val)+point (1327/200) 4096 (16*31+j.val+1))/2) := by
  fin_cases j
  · change cPayment 496 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 496+point (1327/200) 4096 497)/2)
    have hp : cPayment 496 = (63243375278:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 496+point (1327/200) 4096 497)/2 = (3800111:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_496
  · change cPayment 497 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 497+point (1327/200) 4096 498)/2)
    have hp : cPayment 497 = (63313837592:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 497+point (1327/200) 4096 498)/2 = (760233:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_497
  · change cPayment 498 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 498+point (1327/200) 4096 499)/2)
    have hp : cPayment 498 = (63384129813:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 498+point (1327/200) 4096 499)/2 = (3802219:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_498
  · change cPayment 499 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 499+point (1327/200) 4096 500)/2)
    have hp : cPayment 499 = (63454252216:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 499+point (1327/200) 4096 500)/2 = (3803273:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_499
  · change cPayment 500 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 500+point (1327/200) 4096 501)/2)
    have hp : cPayment 500 = (63524205076:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 500+point (1327/200) 4096 501)/2 = (3804327:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_500
  · change cPayment 501 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 501+point (1327/200) 4096 502)/2)
    have hp : cPayment 501 = (63593988668:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 501+point (1327/200) 4096 502)/2 = (3805381:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_501
  · change cPayment 502 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 502+point (1327/200) 4096 503)/2)
    have hp : cPayment 502 = (63663603265:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 502+point (1327/200) 4096 503)/2 = (761287:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_502
  · change cPayment 503 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 503+point (1327/200) 4096 504)/2)
    have hp : cPayment 503 = (63733049142:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 503+point (1327/200) 4096 504)/2 = (3807489:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_503
  · change cPayment 504 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 504+point (1327/200) 4096 505)/2)
    have hp : cPayment 504 = (63802326570:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 504+point (1327/200) 4096 505)/2 = (3808543:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_504
  · change cPayment 505 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 505+point (1327/200) 4096 506)/2)
    have hp : cPayment 505 = (63871435823:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 505+point (1327/200) 4096 506)/2 = (3809597:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_505
  · change cPayment 506 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 506+point (1327/200) 4096 507)/2)
    have hp : cPayment 506 = (63940377173:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 506+point (1327/200) 4096 507)/2 = (3810651:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_506
  · change cPayment 507 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 507+point (1327/200) 4096 508)/2)
    have hp : cPayment 507 = (64009150891:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 507+point (1327/200) 4096 508)/2 = (762341:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_507
  · change cPayment 508 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 508+point (1327/200) 4096 509)/2)
    have hp : cPayment 508 = (64077757248:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 508+point (1327/200) 4096 509)/2 = (3812759:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_508
  · change cPayment 509 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 509+point (1327/200) 4096 510)/2)
    have hp : cPayment 509 = (64146196514:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 509+point (1327/200) 4096 510)/2 = (3813813:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_509
  · change cPayment 510 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 510+point (1327/200) 4096 511)/2)
    have hp : cPayment 510 = (64214468961:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 510+point (1327/200) 4096 511)/2 = (3814867:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_510
  · change cPayment 511 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 511+point (1327/200) 4096 512)/2)
    have hp : cPayment 511 = (64282574857:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 511+point (1327/200) 4096 512)/2 = (3815921:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_511
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_031
