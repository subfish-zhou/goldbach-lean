import WR2ClassicalCPayments
import WR2ClassicalCPoints200
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_200 (j : Fin 16) : cPayment (16*200+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*200+j.val)+point (1327/200) 4096 (16*200+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3200 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3200+point (1327/200) 4096 3201)/2)
    have hp : cPayment 3200 = (29706769144:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3200+point (1327/200) 4096 3201)/2 = (6650127:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3200
  · change cPayment 3201 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3201+point (1327/200) 4096 3202)/2)
    have hp : cPayment 3201 = (29672620862:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3201+point (1327/200) 4096 3202)/2 = (6651181:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3201
  · change cPayment 3202 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3202+point (1327/200) 4096 3203)/2)
    have hp : cPayment 3202 = (29638473512:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3202+point (1327/200) 4096 3203)/2 = (1330447:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3202
  · change cPayment 3203 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3203+point (1327/200) 4096 3204)/2)
    have hp : cPayment 3203 = (29604327100:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3203+point (1327/200) 4096 3204)/2 = (6653289:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3203
  · change cPayment 3204 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3204+point (1327/200) 4096 3205)/2)
    have hp : cPayment 3204 = (29570181630:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3204+point (1327/200) 4096 3205)/2 = (6654343:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3204
  · change cPayment 3205 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3205+point (1327/200) 4096 3206)/2)
    have hp : cPayment 3205 = (29536037109:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3205+point (1327/200) 4096 3206)/2 = (6655397:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3205
  · change cPayment 3206 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3206+point (1327/200) 4096 3207)/2)
    have hp : cPayment 3206 = (29501893542:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3206+point (1327/200) 4096 3207)/2 = (6656451:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3206
  · change cPayment 3207 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3207+point (1327/200) 4096 3208)/2)
    have hp : cPayment 3207 = (29467750935:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3207+point (1327/200) 4096 3208)/2 = (1331501:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3207
  · change cPayment 3208 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3208+point (1327/200) 4096 3209)/2)
    have hp : cPayment 3208 = (29433609293:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3208+point (1327/200) 4096 3209)/2 = (6658559:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3208
  · change cPayment 3209 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3209+point (1327/200) 4096 3210)/2)
    have hp : cPayment 3209 = (29399468622:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3209+point (1327/200) 4096 3210)/2 = (6659613:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3209
  · change cPayment 3210 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3210+point (1327/200) 4096 3211)/2)
    have hp : cPayment 3210 = (29365328927:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3210+point (1327/200) 4096 3211)/2 = (6660667:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3210
  · change cPayment 3211 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3211+point (1327/200) 4096 3212)/2)
    have hp : cPayment 3211 = (29331190214:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3211+point (1327/200) 4096 3212)/2 = (6661721:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3211
  · change cPayment 3212 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3212+point (1327/200) 4096 3213)/2)
    have hp : cPayment 3212 = (29297052488:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3212+point (1327/200) 4096 3213)/2 = (266511:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3212
  · change cPayment 3213 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3213+point (1327/200) 4096 3214)/2)
    have hp : cPayment 3213 = (29262915755:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3213+point (1327/200) 4096 3214)/2 = (6663829:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3213
  · change cPayment 3214 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3214+point (1327/200) 4096 3215)/2)
    have hp : cPayment 3214 = (29228780020:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3214+point (1327/200) 4096 3215)/2 = (6664883:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3214
  · change cPayment 3215 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3215+point (1327/200) 4096 3216)/2)
    have hp : cPayment 3215 = (29194645289:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3215+point (1327/200) 4096 3216)/2 = (6665937:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3215
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_200
