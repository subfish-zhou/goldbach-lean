import WR2ClassicalCPayments
import WR2ClassicalCPoints158
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_158 (j : Fin 16) : cPayment (16*158+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*158+j.val)+point (1327/200) 4096 (16*158+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2528 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2528+point (1327/200) 4096 2529)/2)
    have hp : cPayment 2528 = (52503135404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2528+point (1327/200) 4096 2529)/2 = (5941839:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2528
  · change cPayment 2529 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2529+point (1327/200) 4096 2530)/2)
    have hp : cPayment 2529 = (52470110270:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2529+point (1327/200) 4096 2530)/2 = (5942893:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2529
  · change cPayment 2530 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2530+point (1327/200) 4096 2531)/2)
    have hp : cPayment 2530 = (52437079971:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2530+point (1327/200) 4096 2531)/2 = (5943947:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2530
  · change cPayment 2531 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2531+point (1327/200) 4096 2532)/2)
    have hp : cPayment 2531 = (52404044521:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2531+point (1327/200) 4096 2532)/2 = (5945001:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2531
  · change cPayment 2532 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2532+point (1327/200) 4096 2533)/2)
    have hp : cPayment 2532 = (52371003935:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2532+point (1327/200) 4096 2533)/2 = (1189211:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2532
  · change cPayment 2533 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2533+point (1327/200) 4096 2534)/2)
    have hp : cPayment 2533 = (52337958224:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2533+point (1327/200) 4096 2534)/2 = (5947109:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2533
  · change cPayment 2534 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2534+point (1327/200) 4096 2535)/2)
    have hp : cPayment 2534 = (52304907404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2534+point (1327/200) 4096 2535)/2 = (5948163:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2534
  · change cPayment 2535 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2535+point (1327/200) 4096 2536)/2)
    have hp : cPayment 2535 = (52271851488:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2535+point (1327/200) 4096 2536)/2 = (5949217:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2535
  · change cPayment 2536 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2536+point (1327/200) 4096 2537)/2)
    have hp : cPayment 2536 = (52238790488:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2536+point (1327/200) 4096 2537)/2 = (5950271:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2536
  · change cPayment 2537 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2537+point (1327/200) 4096 2538)/2)
    have hp : cPayment 2537 = (52205724420:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2537+point (1327/200) 4096 2538)/2 = (238053:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2537
  · change cPayment 2538 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2538+point (1327/200) 4096 2539)/2)
    have hp : cPayment 2538 = (52172653297:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2538+point (1327/200) 4096 2539)/2 = (5952379:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2538
  · change cPayment 2539 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2539+point (1327/200) 4096 2540)/2)
    have hp : cPayment 2539 = (52139577131:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2539+point (1327/200) 4096 2540)/2 = (5953433:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2539
  · change cPayment 2540 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2540+point (1327/200) 4096 2541)/2)
    have hp : cPayment 2540 = (52106495937:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2540+point (1327/200) 4096 2541)/2 = (5954487:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2540
  · change cPayment 2541 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2541+point (1327/200) 4096 2542)/2)
    have hp : cPayment 2541 = (52073409729:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2541+point (1327/200) 4096 2542)/2 = (5955541:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2541
  · change cPayment 2542 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2542+point (1327/200) 4096 2543)/2)
    have hp : cPayment 2542 = (52040318519:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2542+point (1327/200) 4096 2543)/2 = (1191319:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2542
  · change cPayment 2543 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2543+point (1327/200) 4096 2544)/2)
    have hp : cPayment 2543 = (52007222321:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2543+point (1327/200) 4096 2544)/2 = (5957649:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2543
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_158
