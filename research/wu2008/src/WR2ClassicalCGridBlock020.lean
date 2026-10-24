import WR2ClassicalCPayments
import WR2ClassicalCPoints020
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_020 (j : Fin 16) : cPayment (16*20+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*20+j.val)+point (1327/200) 4096 (16*20+j.val+1))/2) := by
  fin_cases j
  · change cPayment 320 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 320+point (1327/200) 4096 321)/2)
    have hp : cPayment 320 = (47915994140:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 320+point (1327/200) 4096 321)/2 = (3614607:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_320
  · change cPayment 321 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 321+point (1327/200) 4096 322)/2)
    have hp : cPayment 321 = (48021186343:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 321+point (1327/200) 4096 322)/2 = (3615661:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_321
  · change cPayment 322 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 322+point (1327/200) 4096 323)/2)
    have hp : cPayment 322 = (48126151214:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 322+point (1327/200) 4096 323)/2 = (723343:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_322
  · change cPayment 323 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 323+point (1327/200) 4096 324)/2)
    have hp : cPayment 323 = (48230889132:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 323+point (1327/200) 4096 324)/2 = (3617769:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_323
  · change cPayment 324 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 324+point (1327/200) 4096 325)/2)
    have hp : cPayment 324 = (48335400479:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 324+point (1327/200) 4096 325)/2 = (3618823:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_324
  · change cPayment 325 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 325+point (1327/200) 4096 326)/2)
    have hp : cPayment 325 = (48439685635:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 325+point (1327/200) 4096 326)/2 = (3619877:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_325
  · change cPayment 326 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 326+point (1327/200) 4096 327)/2)
    have hp : cPayment 326 = (48543744977:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 326+point (1327/200) 4096 327)/2 = (3620931:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_326
  · change cPayment 327 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 327+point (1327/200) 4096 328)/2)
    have hp : cPayment 327 = (48647578885:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 327+point (1327/200) 4096 328)/2 = (724397:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_327
  · change cPayment 328 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 328+point (1327/200) 4096 329)/2)
    have hp : cPayment 328 = (48751187735:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 328+point (1327/200) 4096 329)/2 = (3623039:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_328
  · change cPayment 329 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 329+point (1327/200) 4096 330)/2)
    have hp : cPayment 329 = (48854571905:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 329+point (1327/200) 4096 330)/2 = (3624093:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_329
  · change cPayment 330 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 330+point (1327/200) 4096 331)/2)
    have hp : cPayment 330 = (48957731771:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 330+point (1327/200) 4096 331)/2 = (3625147:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_330
  · change cPayment 331 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 331+point (1327/200) 4096 332)/2)
    have hp : cPayment 331 = (49060667709:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 331+point (1327/200) 4096 332)/2 = (3626201:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_331
  · change cPayment 332 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 332+point (1327/200) 4096 333)/2)
    have hp : cPayment 332 = (49163380091:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 332+point (1327/200) 4096 333)/2 = (725451:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_332
  · change cPayment 333 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 333+point (1327/200) 4096 334)/2)
    have hp : cPayment 333 = (49265869294:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 333+point (1327/200) 4096 334)/2 = (3628309:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_333
  · change cPayment 334 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 334+point (1327/200) 4096 335)/2)
    have hp : cPayment 334 = (49368135689:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 334+point (1327/200) 4096 335)/2 = (3629363:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_334
  · change cPayment 335 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 335+point (1327/200) 4096 336)/2)
    have hp : cPayment 335 = (49470179650:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 335+point (1327/200) 4096 336)/2 = (3630417:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_335
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_020
