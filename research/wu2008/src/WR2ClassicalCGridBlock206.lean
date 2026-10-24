import WR2ClassicalCPayments
import WR2ClassicalCPoints206
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_206 (j : Fin 16) : cPayment (16*206+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*206+j.val)+point (1327/200) 4096 (16*206+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3296 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3296+point (1327/200) 4096 3297)/2)
    have hp : cPayment 3296 = (26433555725:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3296+point (1327/200) 4096 3297)/2 = (6751311:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3296
  · change cPayment 3297 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3297+point (1327/200) 4096 3298)/2)
    have hp : cPayment 3297 = (26399521283:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3297+point (1327/200) 4096 3298)/2 = (1350473:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3297
  · change cPayment 3298 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3298+point (1327/200) 4096 3299)/2)
    have hp : cPayment 3298 = (26365488275:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3298+point (1327/200) 4096 3299)/2 = (6753419:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3298
  · change cPayment 3299 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3299+point (1327/200) 4096 3300)/2)
    have hp : cPayment 3299 = (26331456706:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3299+point (1327/200) 4096 3300)/2 = (6754473:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3299
  · change cPayment 3300 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3300+point (1327/200) 4096 3301)/2)
    have hp : cPayment 3300 = (26297426581:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3300+point (1327/200) 4096 3301)/2 = (6755527:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3300
  · change cPayment 3301 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3301+point (1327/200) 4096 3302)/2)
    have hp : cPayment 3301 = (26263397904:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3301+point (1327/200) 4096 3302)/2 = (6756581:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3301
  · change cPayment 3302 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3302+point (1327/200) 4096 3303)/2)
    have hp : cPayment 3302 = (26229370681:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3302+point (1327/200) 4096 3303)/2 = (1351527:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3302
  · change cPayment 3303 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3303+point (1327/200) 4096 3304)/2)
    have hp : cPayment 3303 = (26195344917:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3303+point (1327/200) 4096 3304)/2 = (6758689:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3303
  · change cPayment 3304 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3304+point (1327/200) 4096 3305)/2)
    have hp : cPayment 3304 = (26161320615:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3304+point (1327/200) 4096 3305)/2 = (6759743:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3304
  · change cPayment 3305 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3305+point (1327/200) 4096 3306)/2)
    have hp : cPayment 3305 = (26127297782:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3305+point (1327/200) 4096 3306)/2 = (6760797:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3305
  · change cPayment 3306 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3306+point (1327/200) 4096 3307)/2)
    have hp : cPayment 3306 = (26093276421:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3306+point (1327/200) 4096 3307)/2 = (6761851:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3306
  · change cPayment 3307 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3307+point (1327/200) 4096 3308)/2)
    have hp : cPayment 3307 = (26059256538:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3307+point (1327/200) 4096 3308)/2 = (1352581:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3307
  · change cPayment 3308 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3308+point (1327/200) 4096 3309)/2)
    have hp : cPayment 3308 = (26025238138:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3308+point (1327/200) 4096 3309)/2 = (6763959:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3308
  · change cPayment 3309 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3309+point (1327/200) 4096 3310)/2)
    have hp : cPayment 3309 = (25991221225:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3309+point (1327/200) 4096 3310)/2 = (6765013:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3309
  · change cPayment 3310 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3310+point (1327/200) 4096 3311)/2)
    have hp : cPayment 3310 = (25957205804:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3310+point (1327/200) 4096 3311)/2 = (6766067:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3310
  · change cPayment 3311 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3311+point (1327/200) 4096 3312)/2)
    have hp : cPayment 3311 = (25923191880:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3311+point (1327/200) 4096 3312)/2 = (6767121:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3311
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_206
