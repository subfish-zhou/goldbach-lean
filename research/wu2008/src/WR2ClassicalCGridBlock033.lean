import WR2ClassicalCPayments
import WR2ClassicalCPoints033
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_033 (j : Fin 16) : cPayment (16*33+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*33+j.val)+point (1327/200) 4096 (16*33+j.val+1))/2) := by
  fin_cases j
  · change cPayment 528 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 528+point (1327/200) 4096 529)/2)
    have hp : cPayment 528 = (65415151771:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 528+point (1327/200) 4096 529)/2 = (3833839:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_528
  · change cPayment 529 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 529+point (1327/200) 4096 530)/2)
    have hp : cPayment 529 = (65480305313:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 529+point (1327/200) 4096 530)/2 = (3834893:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_529
  · change cPayment 530 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 530+point (1327/200) 4096 531)/2)
    have hp : cPayment 530 = (65545297338:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 530+point (1327/200) 4096 531)/2 = (3835947:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_530
  · change cPayment 531 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 531+point (1327/200) 4096 532)/2)
    have hp : cPayment 531 = (65610128104:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 531+point (1327/200) 4096 532)/2 = (3837001:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_531
  · change cPayment 532 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 532+point (1327/200) 4096 533)/2)
    have hp : cPayment 532 = (65674797871:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 532+point (1327/200) 4096 533)/2 = (767611:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_532
  · change cPayment 533 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 533+point (1327/200) 4096 534)/2)
    have hp : cPayment 533 = (65739306898:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 533+point (1327/200) 4096 534)/2 = (3839109:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_533
  · change cPayment 534 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 534+point (1327/200) 4096 535)/2)
    have hp : cPayment 534 = (65803655446:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 534+point (1327/200) 4096 535)/2 = (3840163:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_534
  · change cPayment 535 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 535+point (1327/200) 4096 536)/2)
    have hp : cPayment 535 = (65867843770:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 535+point (1327/200) 4096 536)/2 = (3841217:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_535
  · change cPayment 536 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 536+point (1327/200) 4096 537)/2)
    have hp : cPayment 536 = (65931872131:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 536+point (1327/200) 4096 537)/2 = (3842271:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_536
  · change cPayment 537 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 537+point (1327/200) 4096 538)/2)
    have hp : cPayment 537 = (65995740784:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 537+point (1327/200) 4096 538)/2 = (153733:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_537
  · change cPayment 538 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 538+point (1327/200) 4096 539)/2)
    have hp : cPayment 538 = (66059449987:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 538+point (1327/200) 4096 539)/2 = (3844379:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_538
  · change cPayment 539 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 539+point (1327/200) 4096 540)/2)
    have hp : cPayment 539 = (66122999996:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 539+point (1327/200) 4096 540)/2 = (3845433:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_539
  · change cPayment 540 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 540+point (1327/200) 4096 541)/2)
    have hp : cPayment 540 = (66186391068:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 540+point (1327/200) 4096 541)/2 = (3846487:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_540
  · change cPayment 541 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 541+point (1327/200) 4096 542)/2)
    have hp : cPayment 541 = (66249623458:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 541+point (1327/200) 4096 542)/2 = (3847541:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_541
  · change cPayment 542 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 542+point (1327/200) 4096 543)/2)
    have hp : cPayment 542 = (66312697421:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 542+point (1327/200) 4096 543)/2 = (769719:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_542
  · change cPayment 543 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 543+point (1327/200) 4096 544)/2)
    have hp : cPayment 543 = (66375613212:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 543+point (1327/200) 4096 544)/2 = (3849649:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_543
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_033
