import WR2ClassicalCPayments
import WR2ClassicalCPoints213
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_213 (j : Fin 16) : cPayment (16*213+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*213+j.val)+point (1327/200) 4096 (16*213+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3408 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3408+point (1327/200) 4096 3409)/2)
    have hp : cPayment 3408 = (22631684812:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3408+point (1327/200) 4096 3409)/2 = (6869359:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3408
  · change cPayment 3409 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3409+point (1327/200) 4096 3410)/2)
    have hp : cPayment 3409 = (22597839861:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3409+point (1327/200) 4096 3410)/2 = (6870413:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3409
  · change cPayment 3410 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3410+point (1327/200) 4096 3411)/2)
    have hp : cPayment 3410 = (22563996852:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3410+point (1327/200) 4096 3411)/2 = (6871467:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3410
  · change cPayment 3411 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3411+point (1327/200) 4096 3412)/2)
    have hp : cPayment 3411 = (22530155788:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3411+point (1327/200) 4096 3412)/2 = (6872521:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3411
  · change cPayment 3412 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3412+point (1327/200) 4096 3413)/2)
    have hp : cPayment 3412 = (22496316673:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3412+point (1327/200) 4096 3413)/2 = (274943:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3412
  · change cPayment 3413 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3413+point (1327/200) 4096 3414)/2)
    have hp : cPayment 3413 = (22462479512:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3413+point (1327/200) 4096 3414)/2 = (6874629:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3413
  · change cPayment 3414 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3414+point (1327/200) 4096 3415)/2)
    have hp : cPayment 3414 = (22428644309:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3414+point (1327/200) 4096 3415)/2 = (6875683:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3414
  · change cPayment 3415 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3415+point (1327/200) 4096 3416)/2)
    have hp : cPayment 3415 = (22394811067:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3415+point (1327/200) 4096 3416)/2 = (6876737:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3415
  · change cPayment 3416 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3416+point (1327/200) 4096 3417)/2)
    have hp : cPayment 3416 = (22360979792:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3416+point (1327/200) 4096 3417)/2 = (6877791:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3416
  · change cPayment 3417 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3417+point (1327/200) 4096 3418)/2)
    have hp : cPayment 3417 = (22327150486:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3417+point (1327/200) 4096 3418)/2 = (1375769:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3417
  · change cPayment 3418 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3418+point (1327/200) 4096 3419)/2)
    have hp : cPayment 3418 = (22293323155:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3418+point (1327/200) 4096 3419)/2 = (6879899:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3418
  · change cPayment 3419 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3419+point (1327/200) 4096 3420)/2)
    have hp : cPayment 3419 = (22259497803:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3419+point (1327/200) 4096 3420)/2 = (6880953:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3419
  · change cPayment 3420 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3420+point (1327/200) 4096 3421)/2)
    have hp : cPayment 3420 = (22225674433:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3420+point (1327/200) 4096 3421)/2 = (6882007:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3420
  · change cPayment 3421 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3421+point (1327/200) 4096 3422)/2)
    have hp : cPayment 3421 = (22191853050:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3421+point (1327/200) 4096 3422)/2 = (6883061:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3421
  · change cPayment 3422 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3422+point (1327/200) 4096 3423)/2)
    have hp : cPayment 3422 = (22158033657:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3422+point (1327/200) 4096 3423)/2 = (1376823:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3422
  · change cPayment 3423 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3423+point (1327/200) 4096 3424)/2)
    have hp : cPayment 3423 = (22124216259:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3423+point (1327/200) 4096 3424)/2 = (6885169:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3423
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_213
