import WR2ClassicalCPayments
import WR2ClassicalCPoints166
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_166 (j : Fin 16) : cPayment (16*166+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*166+j.val)+point (1327/200) 4096 (16*166+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2656 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2656+point (1327/200) 4096 2657)/2)
    have hp : cPayment 2656 = (48238433279:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2656+point (1327/200) 4096 2657)/2 = (6076751:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2656
  · change cPayment 2657 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2657+point (1327/200) 4096 2658)/2)
    have hp : cPayment 2657 = (48204852567:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2657+point (1327/200) 4096 2658)/2 = (1215561:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2657
  · change cPayment 2658 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2658+point (1327/200) 4096 2659)/2)
    have hp : cPayment 2658 = (48171268306:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2658+point (1327/200) 4096 2659)/2 = (6078859:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2658
  · change cPayment 2659 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2659+point (1327/200) 4096 2660)/2)
    have hp : cPayment 2659 = (48137680507:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2659+point (1327/200) 4096 2660)/2 = (6079913:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2659
  · change cPayment 2660 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2660+point (1327/200) 4096 2661)/2)
    have hp : cPayment 2660 = (48104089182:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2660+point (1327/200) 4096 2661)/2 = (6080967:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2660
  · change cPayment 2661 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2661+point (1327/200) 4096 2662)/2)
    have hp : cPayment 2661 = (48070494343:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2661+point (1327/200) 4096 2662)/2 = (6082021:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2661
  · change cPayment 2662 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2662+point (1327/200) 4096 2663)/2)
    have hp : cPayment 2662 = (48036896000:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2662+point (1327/200) 4096 2663)/2 = (243323:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2662
  · change cPayment 2663 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2663+point (1327/200) 4096 2664)/2)
    have hp : cPayment 2663 = (48003294166:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2663+point (1327/200) 4096 2664)/2 = (6084129:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2663
  · change cPayment 2664 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2664+point (1327/200) 4096 2665)/2)
    have hp : cPayment 2664 = (47969688852:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2664+point (1327/200) 4096 2665)/2 = (6085183:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2664
  · change cPayment 2665 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2665+point (1327/200) 4096 2666)/2)
    have hp : cPayment 2665 = (47936080069:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2665+point (1327/200) 4096 2666)/2 = (6086237:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2665
  · change cPayment 2666 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2666+point (1327/200) 4096 2667)/2)
    have hp : cPayment 2666 = (47902467830:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2666+point (1327/200) 4096 2667)/2 = (6087291:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2666
  · change cPayment 2667 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2667+point (1327/200) 4096 2668)/2)
    have hp : cPayment 2667 = (47868852144:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2667+point (1327/200) 4096 2668)/2 = (1217669:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2667
  · change cPayment 2668 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2668+point (1327/200) 4096 2669)/2)
    have hp : cPayment 2668 = (47835233024:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2668+point (1327/200) 4096 2669)/2 = (6089399:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2668
  · change cPayment 2669 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2669+point (1327/200) 4096 2670)/2)
    have hp : cPayment 2669 = (47801610482:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2669+point (1327/200) 4096 2670)/2 = (6090453:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2669
  · change cPayment 2670 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2670+point (1327/200) 4096 2671)/2)
    have hp : cPayment 2670 = (47767984528:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2670+point (1327/200) 4096 2671)/2 = (6091507:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2670
  · change cPayment 2671 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2671+point (1327/200) 4096 2672)/2)
    have hp : cPayment 2671 = (47734355174:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2671+point (1327/200) 4096 2672)/2 = (6092561:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2671
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_166
