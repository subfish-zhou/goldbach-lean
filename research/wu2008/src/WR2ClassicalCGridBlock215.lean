import WR2ClassicalCPayments
import WR2ClassicalCPoints215
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_215 (j : Fin 16) : cPayment (16*215+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*215+j.val)+point (1327/200) 4096 (16*215+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3440 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3440+point (1327/200) 4096 3441)/2)
    have hp : cPayment 3440 = (21549629672:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3440+point (1327/200) 4096 3441)/2 = (6903087:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3440
  · change cPayment 3441 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3441+point (1327/200) 4096 3442)/2)
    have hp : cPayment 3441 = (21515848879:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3441+point (1327/200) 4096 3442)/2 = (6904141:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3441
  · change cPayment 3442 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3442+point (1327/200) 4096 3443)/2)
    have hp : cPayment 3442 = (21482070157:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3442+point (1327/200) 4096 3443)/2 = (1381039:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3442
  · change cPayment 3443 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3443+point (1327/200) 4096 3444)/2)
    have hp : cPayment 3443 = (21448293511:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3443+point (1327/200) 4096 3444)/2 = (6906249:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3443
  · change cPayment 3444 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3444+point (1327/200) 4096 3445)/2)
    have hp : cPayment 3444 = (21414518945:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3444+point (1327/200) 4096 3445)/2 = (6907303:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3444
  · change cPayment 3445 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3445+point (1327/200) 4096 3446)/2)
    have hp : cPayment 3445 = (21380746462:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3445+point (1327/200) 4096 3446)/2 = (6908357:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3445
  · change cPayment 3446 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3446+point (1327/200) 4096 3447)/2)
    have hp : cPayment 3446 = (21346976068:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3446+point (1327/200) 4096 3447)/2 = (6909411:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3446
  · change cPayment 3447 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3447+point (1327/200) 4096 3448)/2)
    have hp : cPayment 3447 = (21313207765:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3447+point (1327/200) 4096 3448)/2 = (1382093:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3447
  · change cPayment 3448 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3448+point (1327/200) 4096 3449)/2)
    have hp : cPayment 3448 = (21279441557:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3448+point (1327/200) 4096 3449)/2 = (6911519:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3448
  · change cPayment 3449 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3449+point (1327/200) 4096 3450)/2)
    have hp : cPayment 3449 = (21245677450:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3449+point (1327/200) 4096 3450)/2 = (6912573:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3449
  · change cPayment 3450 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3450+point (1327/200) 4096 3451)/2)
    have hp : cPayment 3450 = (21211915446:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3450+point (1327/200) 4096 3451)/2 = (6913627:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3450
  · change cPayment 3451 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3451+point (1327/200) 4096 3452)/2)
    have hp : cPayment 3451 = (21178155550:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3451+point (1327/200) 4096 3452)/2 = (6914681:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3451
  · change cPayment 3452 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3452+point (1327/200) 4096 3453)/2)
    have hp : cPayment 3452 = (21144397765:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3452+point (1327/200) 4096 3453)/2 = (1383147:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3452
  · change cPayment 3453 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3453+point (1327/200) 4096 3454)/2)
    have hp : cPayment 3453 = (21110642095:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3453+point (1327/200) 4096 3454)/2 = (6916789:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3453
  · change cPayment 3454 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3454+point (1327/200) 4096 3455)/2)
    have hp : cPayment 3454 = (21076888545:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3454+point (1327/200) 4096 3455)/2 = (6917843:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3454
  · change cPayment 3455 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3455+point (1327/200) 4096 3456)/2)
    have hp : cPayment 3455 = (21043137118:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3455+point (1327/200) 4096 3456)/2 = (6918897:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3455
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_215
