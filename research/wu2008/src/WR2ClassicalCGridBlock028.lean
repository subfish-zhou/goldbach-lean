import WR2ClassicalCPayments
import WR2ClassicalCPoints028
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_028 (j : Fin 16) : cPayment (16*28+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*28+j.val)+point (1327/200) 4096 (16*28+j.val+1))/2) := by
  fin_cases j
  · change cPayment 448 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 448+point (1327/200) 4096 449)/2)
    have hp : cPayment 448 = (59655629536:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 448+point (1327/200) 4096 449)/2 = (3749519:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_448
  · change cPayment 449 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 449+point (1327/200) 4096 450)/2)
    have hp : cPayment 449 = (59734590199:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 449+point (1327/200) 4096 450)/2 = (3750573:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_449
  · change cPayment 450 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 450+point (1327/200) 4096 451)/2)
    have hp : cPayment 450 = (59813366946:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 450+point (1327/200) 4096 451)/2 = (3751627:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_450
  · change cPayment 451 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 451+point (1327/200) 4096 452)/2)
    have hp : cPayment 451 = (59891960077:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 451+point (1327/200) 4096 452)/2 = (3752681:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_451
  · change cPayment 452 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 452+point (1327/200) 4096 453)/2)
    have hp : cPayment 452 = (59970369891:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 452+point (1327/200) 4096 453)/2 = (750747:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_452
  · change cPayment 453 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 453+point (1327/200) 4096 454)/2)
    have hp : cPayment 453 = (60048596689:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 453+point (1327/200) 4096 454)/2 = (3754789:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_453
  · change cPayment 454 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 454+point (1327/200) 4096 455)/2)
    have hp : cPayment 454 = (60126640769:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 454+point (1327/200) 4096 455)/2 = (3755843:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_454
  · change cPayment 455 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 455+point (1327/200) 4096 456)/2)
    have hp : cPayment 455 = (60204502429:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 455+point (1327/200) 4096 456)/2 = (3756897:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_455
  · change cPayment 456 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 456+point (1327/200) 4096 457)/2)
    have hp : cPayment 456 = (60282181967:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 456+point (1327/200) 4096 457)/2 = (3757951:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_456
  · change cPayment 457 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 457+point (1327/200) 4096 458)/2)
    have hp : cPayment 457 = (60359679680:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 457+point (1327/200) 4096 458)/2 = (751801:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_457
  · change cPayment 458 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 458+point (1327/200) 4096 459)/2)
    have hp : cPayment 458 = (60436995865:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 458+point (1327/200) 4096 459)/2 = (3760059:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_458
  · change cPayment 459 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 459+point (1327/200) 4096 460)/2)
    have hp : cPayment 459 = (60514130818:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 459+point (1327/200) 4096 460)/2 = (3761113:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_459
  · change cPayment 460 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 460+point (1327/200) 4096 461)/2)
    have hp : cPayment 460 = (60591084834:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 460+point (1327/200) 4096 461)/2 = (3762167:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_460
  · change cPayment 461 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 461+point (1327/200) 4096 462)/2)
    have hp : cPayment 461 = (60667858208:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 461+point (1327/200) 4096 462)/2 = (3763221:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_461
  · change cPayment 462 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 462+point (1327/200) 4096 463)/2)
    have hp : cPayment 462 = (60744451235:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 462+point (1327/200) 4096 463)/2 = (150571:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_462
  · change cPayment 463 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 463+point (1327/200) 4096 464)/2)
    have hp : cPayment 463 = (60820864209:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 463+point (1327/200) 4096 464)/2 = (3765329:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_463
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_028
