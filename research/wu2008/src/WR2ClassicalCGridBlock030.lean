import WR2ClassicalCPayments
import WR2ClassicalCPoints030
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_030 (j : Fin 16) : cPayment (16*30+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*30+j.val)+point (1327/200) 4096 (16*30+j.val+1))/2) := by
  fin_cases j
  · change cPayment 480 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 480+point (1327/200) 4096 481)/2)
    have hp : cPayment 480 = (62092618866:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 480+point (1327/200) 4096 481)/2 = (3783247:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_480
  · change cPayment 481 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 481+point (1327/200) 4096 482)/2)
    have hp : cPayment 481 = (62165840541:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 481+point (1327/200) 4096 482)/2 = (3784301:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_481
  · change cPayment 482 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 482+point (1327/200) 4096 483)/2)
    have hp : cPayment 482 = (62238887648:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 482+point (1327/200) 4096 483)/2 = (757071:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_482
  · change cPayment 483 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 483+point (1327/200) 4096 484)/2)
    have hp : cPayment 483 = (62311760469:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 483+point (1327/200) 4096 484)/2 = (3786409:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_483
  · change cPayment 484 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 484+point (1327/200) 4096 485)/2)
    have hp : cPayment 484 = (62384459289:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 484+point (1327/200) 4096 485)/2 = (3787463:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_484
  · change cPayment 485 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 485+point (1327/200) 4096 486)/2)
    have hp : cPayment 485 = (62456984389:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 485+point (1327/200) 4096 486)/2 = (3788517:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_485
  · change cPayment 486 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 486+point (1327/200) 4096 487)/2)
    have hp : cPayment 486 = (62529336051:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 486+point (1327/200) 4096 487)/2 = (3789571:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_486
  · change cPayment 487 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 487+point (1327/200) 4096 488)/2)
    have hp : cPayment 487 = (62601514557:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 487+point (1327/200) 4096 488)/2 = (151625:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_487
  · change cPayment 488 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 488+point (1327/200) 4096 489)/2)
    have hp : cPayment 488 = (62673520188:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 488+point (1327/200) 4096 489)/2 = (3791679:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_488
  · change cPayment 489 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 489+point (1327/200) 4096 490)/2)
    have hp : cPayment 489 = (62745353224:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 489+point (1327/200) 4096 490)/2 = (3792733:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_489
  · change cPayment 490 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 490+point (1327/200) 4096 491)/2)
    have hp : cPayment 490 = (62817013946:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 490+point (1327/200) 4096 491)/2 = (3793787:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_490
  · change cPayment 491 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 491+point (1327/200) 4096 492)/2)
    have hp : cPayment 491 = (62888502632:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 491+point (1327/200) 4096 492)/2 = (3794841:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_491
  · change cPayment 492 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 492+point (1327/200) 4096 493)/2)
    have hp : cPayment 492 = (62959819562:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 492+point (1327/200) 4096 493)/2 = (759179:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_492
  · change cPayment 493 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 493+point (1327/200) 4096 494)/2)
    have hp : cPayment 493 = (63030965014:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 493+point (1327/200) 4096 494)/2 = (3796949:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_493
  · change cPayment 494 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 494+point (1327/200) 4096 495)/2)
    have hp : cPayment 494 = (63101939265:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 494+point (1327/200) 4096 495)/2 = (3798003:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_494
  · change cPayment 495 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 495+point (1327/200) 4096 496)/2)
    have hp : cPayment 495 = (63172742594:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 495+point (1327/200) 4096 496)/2 = (3799057:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_495
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_030
