import WR2ClassicalCPayments
import WR2ClassicalCPoints156
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_156 (j : Fin 16) : cPayment (16*156+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*156+j.val)+point (1327/200) 4096 (16*156+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2496 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2496+point (1327/200) 4096 2497)/2)
    have hp : cPayment 2496 = (53557129758:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2496+point (1327/200) 4096 2497)/2 = (5908111:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2496
  · change cPayment 2497 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2497+point (1327/200) 4096 2498)/2)
    have hp : cPayment 2497 = (53524277241:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2497+point (1327/200) 4096 2498)/2 = (1181833:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2497
  · change cPayment 2498 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2498+point (1327/200) 4096 2499)/2)
    have hp : cPayment 2498 = (53491419112:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2498+point (1327/200) 4096 2499)/2 = (5910219:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2498
  · change cPayment 2499 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2499+point (1327/200) 4096 2500)/2)
    have hp : cPayment 2499 = (53458555383:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2499+point (1327/200) 4096 2500)/2 = (5911273:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2499
  · change cPayment 2500 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2500+point (1327/200) 4096 2501)/2)
    have hp : cPayment 2500 = (53425686071:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2500+point (1327/200) 4096 2501)/2 = (5912327:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2500
  · change cPayment 2501 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2501+point (1327/200) 4096 2502)/2)
    have hp : cPayment 2501 = (53392811188:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2501+point (1327/200) 4096 2502)/2 = (5913381:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2501
  · change cPayment 2502 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2502+point (1327/200) 4096 2503)/2)
    have hp : cPayment 2502 = (53359930749:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2502+point (1327/200) 4096 2503)/2 = (1182887:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2502
  · change cPayment 2503 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2503+point (1327/200) 4096 2504)/2)
    have hp : cPayment 2503 = (53327044768:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2503+point (1327/200) 4096 2504)/2 = (5915489:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2503
  · change cPayment 2504 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2504+point (1327/200) 4096 2505)/2)
    have hp : cPayment 2504 = (53294153259:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2504+point (1327/200) 4096 2505)/2 = (5916543:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2504
  · change cPayment 2505 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2505+point (1327/200) 4096 2506)/2)
    have hp : cPayment 2505 = (53261256237:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2505+point (1327/200) 4096 2506)/2 = (5917597:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2505
  · change cPayment 2506 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2506+point (1327/200) 4096 2507)/2)
    have hp : cPayment 2506 = (53228353716:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2506+point (1327/200) 4096 2507)/2 = (5918651:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2506
  · change cPayment 2507 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2507+point (1327/200) 4096 2508)/2)
    have hp : cPayment 2507 = (53195445710:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2507+point (1327/200) 4096 2508)/2 = (1183941:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2507
  · change cPayment 2508 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2508+point (1327/200) 4096 2509)/2)
    have hp : cPayment 2508 = (53162532233:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2508+point (1327/200) 4096 2509)/2 = (5920759:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2508
  · change cPayment 2509 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2509+point (1327/200) 4096 2510)/2)
    have hp : cPayment 2509 = (53129613300:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2509+point (1327/200) 4096 2510)/2 = (5921813:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2509
  · change cPayment 2510 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2510+point (1327/200) 4096 2511)/2)
    have hp : cPayment 2510 = (53096688923:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2510+point (1327/200) 4096 2511)/2 = (5922867:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2510
  · change cPayment 2511 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2511+point (1327/200) 4096 2512)/2)
    have hp : cPayment 2511 = (53063759118:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2511+point (1327/200) 4096 2512)/2 = (5923921:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2511
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_156
