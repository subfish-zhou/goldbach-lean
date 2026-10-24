import WR2ClassicalCPayments
import WR2ClassicalCPoints169
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_169 (j : Fin 16) : cPayment (16*169+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*169+j.val)+point (1327/200) 4096 (16*169+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2704 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2704+point (1327/200) 4096 2705)/2)
    have hp : cPayment 2704 = (46622752756:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2704+point (1327/200) 4096 2705)/2 = (6127343:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2704
  · change cPayment 2705 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2705+point (1327/200) 4096 2706)/2)
    have hp : cPayment 2705 = (46589014473:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2705+point (1327/200) 4096 2706)/2 = (6128397:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2705
  · change cPayment 2706 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2706+point (1327/200) 4096 2707)/2)
    have hp : cPayment 2706 = (46555273178:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2706+point (1327/200) 4096 2707)/2 = (6129451:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2706
  · change cPayment 2707 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2707+point (1327/200) 4096 2708)/2)
    have hp : cPayment 2707 = (46521528884:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2707+point (1327/200) 4096 2708)/2 = (1226101:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2707
  · change cPayment 2708 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2708+point (1327/200) 4096 2709)/2)
    have hp : cPayment 2708 = (46487781601:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2708+point (1327/200) 4096 2709)/2 = (6131559:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2708
  · change cPayment 2709 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2709+point (1327/200) 4096 2710)/2)
    have hp : cPayment 2709 = (46454031339:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2709+point (1327/200) 4096 2710)/2 = (6132613:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2709
  · change cPayment 2710 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2710+point (1327/200) 4096 2711)/2)
    have hp : cPayment 2710 = (46420278111:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2710+point (1327/200) 4096 2711)/2 = (6133667:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2710
  · change cPayment 2711 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2711+point (1327/200) 4096 2712)/2)
    have hp : cPayment 2711 = (46386521925:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2711+point (1327/200) 4096 2712)/2 = (6134721:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2711
  · change cPayment 2712 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2712+point (1327/200) 4096 2713)/2)
    have hp : cPayment 2712 = (46352762794:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2712+point (1327/200) 4096 2713)/2 = (245431:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2712
  · change cPayment 2713 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2713+point (1327/200) 4096 2714)/2)
    have hp : cPayment 2713 = (46319000728:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2713+point (1327/200) 4096 2714)/2 = (6136829:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2713
  · change cPayment 2714 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2714+point (1327/200) 4096 2715)/2)
    have hp : cPayment 2714 = (46285235738:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2714+point (1327/200) 4096 2715)/2 = (6137883:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2714
  · change cPayment 2715 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2715+point (1327/200) 4096 2716)/2)
    have hp : cPayment 2715 = (46251467834:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2715+point (1327/200) 4096 2716)/2 = (6138937:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2715
  · change cPayment 2716 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2716+point (1327/200) 4096 2717)/2)
    have hp : cPayment 2716 = (46217697028:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2716+point (1327/200) 4096 2717)/2 = (6139991:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2716
  · change cPayment 2717 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2717+point (1327/200) 4096 2718)/2)
    have hp : cPayment 2717 = (46183923329:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2717+point (1327/200) 4096 2718)/2 = (1228209:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2717
  · change cPayment 2718 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2718+point (1327/200) 4096 2719)/2)
    have hp : cPayment 2718 = (46150146749:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2718+point (1327/200) 4096 2719)/2 = (6142099:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2718
  · change cPayment 2719 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2719+point (1327/200) 4096 2720)/2)
    have hp : cPayment 2719 = (46116367298:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2719+point (1327/200) 4096 2720)/2 = (6143153:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2719
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_169
