import WR2ClassicalCPayments
import WR2ClassicalCPoints216
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_216 (j : Fin 16) : cPayment (16*216+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*216+j.val)+point (1327/200) 4096 (16*216+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3456 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3456+point (1327/200) 4096 3457)/2)
    have hp : cPayment 3456 = (21009387819:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3456+point (1327/200) 4096 3457)/2 = (6919951:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3456
  · change cPayment 3457 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3457+point (1327/200) 4096 3458)/2)
    have hp : cPayment 3457 = (20975640650:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3457+point (1327/200) 4096 3458)/2 = (1384201:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3457
  · change cPayment 3458 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3458+point (1327/200) 4096 3459)/2)
    have hp : cPayment 3458 = (20941895617:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3458+point (1327/200) 4096 3459)/2 = (6922059:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3458
  · change cPayment 3459 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3459+point (1327/200) 4096 3460)/2)
    have hp : cPayment 3459 = (20908152722:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3459+point (1327/200) 4096 3460)/2 = (6923113:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3459
  · change cPayment 3460 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3460+point (1327/200) 4096 3461)/2)
    have hp : cPayment 3460 = (20874411971:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3460+point (1327/200) 4096 3461)/2 = (6924167:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3460
  · change cPayment 3461 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3461+point (1327/200) 4096 3462)/2)
    have hp : cPayment 3461 = (20840673366:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3461+point (1327/200) 4096 3462)/2 = (6925221:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3461
  · change cPayment 3462 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3462+point (1327/200) 4096 3463)/2)
    have hp : cPayment 3462 = (20806936911:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3462+point (1327/200) 4096 3463)/2 = (277051:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3462
  · change cPayment 3463 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3463+point (1327/200) 4096 3464)/2)
    have hp : cPayment 3463 = (20773202611:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3463+point (1327/200) 4096 3464)/2 = (6927329:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3463
  · change cPayment 3464 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3464+point (1327/200) 4096 3465)/2)
    have hp : cPayment 3464 = (20739470470:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3464+point (1327/200) 4096 3465)/2 = (6928383:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3464
  · change cPayment 3465 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3465+point (1327/200) 4096 3466)/2)
    have hp : cPayment 3465 = (20705740490:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3465+point (1327/200) 4096 3466)/2 = (6929437:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3465
  · change cPayment 3466 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3466+point (1327/200) 4096 3467)/2)
    have hp : cPayment 3466 = (20672012677:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3466+point (1327/200) 4096 3467)/2 = (6930491:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3466
  · change cPayment 3467 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3467+point (1327/200) 4096 3468)/2)
    have hp : cPayment 3467 = (20638287034:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3467+point (1327/200) 4096 3468)/2 = (1386309:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3467
  · change cPayment 3468 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3468+point (1327/200) 4096 3469)/2)
    have hp : cPayment 3468 = (20604563564:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3468+point (1327/200) 4096 3469)/2 = (6932599:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3468
  · change cPayment 3469 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3469+point (1327/200) 4096 3470)/2)
    have hp : cPayment 3469 = (20570842272:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3469+point (1327/200) 4096 3470)/2 = (6933653:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3469
  · change cPayment 3470 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3470+point (1327/200) 4096 3471)/2)
    have hp : cPayment 3470 = (20537123162:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3470+point (1327/200) 4096 3471)/2 = (6934707:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3470
  · change cPayment 3471 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3471+point (1327/200) 4096 3472)/2)
    have hp : cPayment 3471 = (20503406236:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3471+point (1327/200) 4096 3472)/2 = (6935761:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3471
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_216
