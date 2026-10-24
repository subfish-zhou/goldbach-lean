import WR2ClassicalCPayments
import WR2ClassicalCPoints162
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_162 (j : Fin 16) : cPayment (16*162+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*162+j.val)+point (1327/200) 4096 (16*162+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2592 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2592+point (1327/200) 4096 2593)/2)
    have hp : cPayment 2592 = (50379674828:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2592+point (1327/200) 4096 2593)/2 = (1201859:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2592
  · change cPayment 2593 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2593+point (1327/200) 4096 2594)/2)
    have hp : cPayment 2593 = (50346346058:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2593+point (1327/200) 4096 2594)/2 = (6010349:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2593
  · change cPayment 2594 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2594+point (1327/200) 4096 2595)/2)
    have hp : cPayment 2594 = (50313012965:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2594+point (1327/200) 4096 2595)/2 = (6011403:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2594
  · change cPayment 2595 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2595+point (1327/200) 4096 2596)/2)
    have hp : cPayment 2595 = (50279675561:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2595+point (1327/200) 4096 2596)/2 = (6012457:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2595
  · change cPayment 2596 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2596+point (1327/200) 4096 2597)/2)
    have hp : cPayment 2596 = (50246333861:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2596+point (1327/200) 4096 2597)/2 = (6013511:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2596
  · change cPayment 2597 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2597+point (1327/200) 4096 2598)/2)
    have hp : cPayment 2597 = (50212987875:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2597+point (1327/200) 4096 2598)/2 = (1202913:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2597
  · change cPayment 2598 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2598+point (1327/200) 4096 2599)/2)
    have hp : cPayment 2598 = (50179637616:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2598+point (1327/200) 4096 2599)/2 = (6015619:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2598
  · change cPayment 2599 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2599+point (1327/200) 4096 2600)/2)
    have hp : cPayment 2599 = (50146283098:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2599+point (1327/200) 4096 2600)/2 = (6016673:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2599
  · change cPayment 2600 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2600+point (1327/200) 4096 2601)/2)
    have hp : cPayment 2600 = (50112924333:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2600+point (1327/200) 4096 2601)/2 = (6017727:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2600
  · change cPayment 2601 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2601+point (1327/200) 4096 2602)/2)
    have hp : cPayment 2601 = (50079561332:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2601+point (1327/200) 4096 2602)/2 = (6018781:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2601
  · change cPayment 2602 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2602+point (1327/200) 4096 2603)/2)
    have hp : cPayment 2602 = (50046194109:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2602+point (1327/200) 4096 2603)/2 = (1203967:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2602
  · change cPayment 2603 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2603+point (1327/200) 4096 2604)/2)
    have hp : cPayment 2603 = (50012822676:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2603+point (1327/200) 4096 2604)/2 = (6020889:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2603
  · change cPayment 2604 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2604+point (1327/200) 4096 2605)/2)
    have hp : cPayment 2604 = (49979447046:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2604+point (1327/200) 4096 2605)/2 = (6021943:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2604
  · change cPayment 2605 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2605+point (1327/200) 4096 2606)/2)
    have hp : cPayment 2605 = (49946067230:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2605+point (1327/200) 4096 2606)/2 = (6022997:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2605
  · change cPayment 2606 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2606+point (1327/200) 4096 2607)/2)
    have hp : cPayment 2606 = (49912683242:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2606+point (1327/200) 4096 2607)/2 = (6024051:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2606
  · change cPayment 2607 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2607+point (1327/200) 4096 2608)/2)
    have hp : cPayment 2607 = (49879295093:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2607+point (1327/200) 4096 2608)/2 = (1205021:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2607
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_162
