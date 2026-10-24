import WR2ClassicalCPayments
import WR2ClassicalCPoints208
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_208 (j : Fin 16) : cPayment (16*208+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*208+j.val)+point (1327/200) 4096 (16*208+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3328 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3328+point (1327/200) 4096 3329)/2)
    have hp : cPayment 3328 = (25345188842:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3328+point (1327/200) 4096 3329)/2 = (6785039:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3328
  · change cPayment 3329 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3329+point (1327/200) 4096 3330)/2)
    have hp : cPayment 3329 = (25311202678:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3329+point (1327/200) 4096 3330)/2 = (6786093:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3329
  · change cPayment 3330 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3330+point (1327/200) 4096 3331)/2)
    have hp : cPayment 3330 = (25277218102:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3330+point (1327/200) 4096 3331)/2 = (6787147:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3330
  · change cPayment 3331 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3331+point (1327/200) 4096 3332)/2)
    have hp : cPayment 3331 = (25243235117:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3331+point (1327/200) 4096 3332)/2 = (6788201:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3331
  · change cPayment 3332 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3332+point (1327/200) 4096 3333)/2)
    have hp : cPayment 3332 = (25209253729:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3332+point (1327/200) 4096 3333)/2 = (1357851:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3332
  · change cPayment 3333 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3333+point (1327/200) 4096 3334)/2)
    have hp : cPayment 3333 = (25175273942:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3333+point (1327/200) 4096 3334)/2 = (6790309:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3333
  · change cPayment 3334 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3334+point (1327/200) 4096 3335)/2)
    have hp : cPayment 3334 = (25141295760:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3334+point (1327/200) 4096 3335)/2 = (6791363:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3334
  · change cPayment 3335 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3335+point (1327/200) 4096 3336)/2)
    have hp : cPayment 3335 = (25107319189:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3335+point (1327/200) 4096 3336)/2 = (6792417:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3335
  · change cPayment 3336 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3336+point (1327/200) 4096 3337)/2)
    have hp : cPayment 3336 = (25073344233:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3336+point (1327/200) 4096 3337)/2 = (6793471:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3336
  · change cPayment 3337 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3337+point (1327/200) 4096 3338)/2)
    have hp : cPayment 3337 = (25039370896:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3337+point (1327/200) 4096 3338)/2 = (271781:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3337
  · change cPayment 3338 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3338+point (1327/200) 4096 3339)/2)
    have hp : cPayment 3338 = (25005399184:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3338+point (1327/200) 4096 3339)/2 = (6795579:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3338
  · change cPayment 3339 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3339+point (1327/200) 4096 3340)/2)
    have hp : cPayment 3339 = (24971429101:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3339+point (1327/200) 4096 3340)/2 = (6796633:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3339
  · change cPayment 3340 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3340+point (1327/200) 4096 3341)/2)
    have hp : cPayment 3340 = (24937460651:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3340+point (1327/200) 4096 3341)/2 = (6797687:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3340
  · change cPayment 3341 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3341+point (1327/200) 4096 3342)/2)
    have hp : cPayment 3341 = (24903493839:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3341+point (1327/200) 4096 3342)/2 = (6798741:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3341
  · change cPayment 3342 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3342+point (1327/200) 4096 3343)/2)
    have hp : cPayment 3342 = (24869528670:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3342+point (1327/200) 4096 3343)/2 = (1359959:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3342
  · change cPayment 3343 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3343+point (1327/200) 4096 3344)/2)
    have hp : cPayment 3343 = (24835565149:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3343+point (1327/200) 4096 3344)/2 = (6800849:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3343
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_208
