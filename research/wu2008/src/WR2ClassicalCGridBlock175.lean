import WR2ClassicalCPayments
import WR2ClassicalCPoints175
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_175 (j : Fin 16) : cPayment (16*175+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*175+j.val)+point (1327/200) 4096 (16*175+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2800 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2800+point (1327/200) 4096 2801)/2)
    have hp : cPayment 2800 = (43371653618:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2800+point (1327/200) 4096 2801)/2 = (6228527:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2800
  · change cPayment 2801 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2801+point (1327/200) 4096 2802)/2)
    have hp : cPayment 2801 = (43337673831:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2801+point (1327/200) 4096 2802)/2 = (6229581:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2801
  · change cPayment 2802 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2802+point (1327/200) 4096 2803)/2)
    have hp : cPayment 2802 = (43303692012:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2802+point (1327/200) 4096 2803)/2 = (1246127:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2802
  · change cPayment 2803 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2803+point (1327/200) 4096 2804)/2)
    have hp : cPayment 2803 = (43269708172:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2803+point (1327/200) 4096 2804)/2 = (6231689:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2803
  · change cPayment 2804 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2804+point (1327/200) 4096 2805)/2)
    have hp : cPayment 2804 = (43235722320:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2804+point (1327/200) 4096 2805)/2 = (6232743:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2804
  · change cPayment 2805 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2805+point (1327/200) 4096 2806)/2)
    have hp : cPayment 2805 = (43201734465:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2805+point (1327/200) 4096 2806)/2 = (6233797:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2805
  · change cPayment 2806 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2806+point (1327/200) 4096 2807)/2)
    have hp : cPayment 2806 = (43167744617:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2806+point (1327/200) 4096 2807)/2 = (6234851:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2806
  · change cPayment 2807 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2807+point (1327/200) 4096 2808)/2)
    have hp : cPayment 2807 = (43133752786:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2807+point (1327/200) 4096 2808)/2 = (1247181:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2807
  · change cPayment 2808 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2808+point (1327/200) 4096 2809)/2)
    have hp : cPayment 2808 = (43099758980:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2808+point (1327/200) 4096 2809)/2 = (6236959:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2808
  · change cPayment 2809 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2809+point (1327/200) 4096 2810)/2)
    have hp : cPayment 2809 = (43065763210:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2809+point (1327/200) 4096 2810)/2 = (6238013:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2809
  · change cPayment 2810 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2810+point (1327/200) 4096 2811)/2)
    have hp : cPayment 2810 = (43031765485:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2810+point (1327/200) 4096 2811)/2 = (6239067:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2810
  · change cPayment 2811 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2811+point (1327/200) 4096 2812)/2)
    have hp : cPayment 2811 = (42997765814:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2811+point (1327/200) 4096 2812)/2 = (6240121:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2811
  · change cPayment 2812 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2812+point (1327/200) 4096 2813)/2)
    have hp : cPayment 2812 = (42963764208:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2812+point (1327/200) 4096 2813)/2 = (249647:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2812
  · change cPayment 2813 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2813+point (1327/200) 4096 2814)/2)
    have hp : cPayment 2813 = (42929760674:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2813+point (1327/200) 4096 2814)/2 = (6242229:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2813
  · change cPayment 2814 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2814+point (1327/200) 4096 2815)/2)
    have hp : cPayment 2814 = (42895755223:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2814+point (1327/200) 4096 2815)/2 = (6243283:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2814
  · change cPayment 2815 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2815+point (1327/200) 4096 2816)/2)
    have hp : cPayment 2815 = (42861747864:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2815+point (1327/200) 4096 2816)/2 = (6244337:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2815
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_175
