import WR2ClassicalCPayments
import WR2ClassicalCPoints036
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_036 (j : Fin 16) : cPayment (16*36+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*36+j.val)+point (1327/200) 4096 (16*36+j.val+1))/2) := by
  fin_cases j
  · change cPayment 576 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 576+point (1327/200) 4096 577)/2)
    have hp : cPayment 576 = (68364740442:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 576+point (1327/200) 4096 577)/2 = (3884431:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_576
  · change cPayment 577 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 577+point (1327/200) 4096 578)/2)
    have hp : cPayment 577 = (68422426754:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 577+point (1327/200) 4096 578)/2 = (777097:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_577
  · change cPayment 578 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 578+point (1327/200) 4096 579)/2)
    have hp : cPayment 578 = (68479963530:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 578+point (1327/200) 4096 579)/2 = (3886539:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_578
  · change cPayment 579 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 579+point (1327/200) 4096 580)/2)
    have hp : cPayment 579 = (68537351010:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 579+point (1327/200) 4096 580)/2 = (3887593:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_579
  · change cPayment 580 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 580+point (1327/200) 4096 581)/2)
    have hp : cPayment 580 = (68594589433:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 580+point (1327/200) 4096 581)/2 = (3888647:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_580
  · change cPayment 581 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 581+point (1327/200) 4096 582)/2)
    have hp : cPayment 581 = (68651679035:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 581+point (1327/200) 4096 582)/2 = (3889701:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_581
  · change cPayment 582 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 582+point (1327/200) 4096 583)/2)
    have hp : cPayment 582 = (68708620056:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 582+point (1327/200) 4096 583)/2 = (778151:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_582
  · change cPayment 583 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 583+point (1327/200) 4096 584)/2)
    have hp : cPayment 583 = (68765412733:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 583+point (1327/200) 4096 584)/2 = (3891809:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_583
  · change cPayment 584 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 584+point (1327/200) 4096 585)/2)
    have hp : cPayment 584 = (68822057302:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 584+point (1327/200) 4096 585)/2 = (3892863:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_584
  · change cPayment 585 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 585+point (1327/200) 4096 586)/2)
    have hp : cPayment 585 = (68878554000:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 585+point (1327/200) 4096 586)/2 = (3893917:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_585
  · change cPayment 586 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 586+point (1327/200) 4096 587)/2)
    have hp : cPayment 586 = (68934903063:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 586+point (1327/200) 4096 587)/2 = (3894971:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_586
  · change cPayment 587 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 587+point (1327/200) 4096 588)/2)
    have hp : cPayment 587 = (68991104727:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 587+point (1327/200) 4096 588)/2 = (155841:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_587
  · change cPayment 588 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 588+point (1327/200) 4096 589)/2)
    have hp : cPayment 588 = (69047159227:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 588+point (1327/200) 4096 589)/2 = (3897079:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_588
  · change cPayment 589 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 589+point (1327/200) 4096 590)/2)
    have hp : cPayment 589 = (69103066799:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 589+point (1327/200) 4096 590)/2 = (3898133:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_589
  · change cPayment 590 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 590+point (1327/200) 4096 591)/2)
    have hp : cPayment 590 = (69158827676:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 590+point (1327/200) 4096 591)/2 = (3899187:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_590
  · change cPayment 591 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 591+point (1327/200) 4096 592)/2)
    have hp : cPayment 591 = (69214442092:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 591+point (1327/200) 4096 592)/2 = (3900241:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_591
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_036
