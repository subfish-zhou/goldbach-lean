import WR2ClassicalCPayments
import WR2ClassicalCPoints223
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_223 (j : Fin 16) : cPayment (16*223+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*223+j.val)+point (1327/200) 4096 (16*223+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3568 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3568+point (1327/200) 4096 3569)/2)
    have hp : cPayment 3568 = (17243831739:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3568+point (1327/200) 4096 3569)/2 = (7037999:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3568
  · change cPayment 3569 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3569+point (1327/200) 4096 3570)/2)
    have hp : cPayment 3569 = (17210346716:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3569+point (1327/200) 4096 3570)/2 = (7039053:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3569
  · change cPayment 3570 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3570+point (1327/200) 4096 3571)/2)
    have hp : cPayment 3570 = (17176864231:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3570+point (1327/200) 4096 3571)/2 = (7040107:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3570
  · change cPayment 3571 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3571+point (1327/200) 4096 3572)/2)
    have hp : cPayment 3571 = (17143384288:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3571+point (1327/200) 4096 3572)/2 = (7041161:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3571
  · change cPayment 3572 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3572+point (1327/200) 4096 3573)/2)
    have hp : cPayment 3572 = (17109906890:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3572+point (1327/200) 4096 3573)/2 = (1408443:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3572
  · change cPayment 3573 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3573+point (1327/200) 4096 3574)/2)
    have hp : cPayment 3573 = (17076432042:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3573+point (1327/200) 4096 3574)/2 = (7043269:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3573
  · change cPayment 3574 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3574+point (1327/200) 4096 3575)/2)
    have hp : cPayment 3574 = (17042959745:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3574+point (1327/200) 4096 3575)/2 = (7044323:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3574
  · change cPayment 3575 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3575+point (1327/200) 4096 3576)/2)
    have hp : cPayment 3575 = (17009490004:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3575+point (1327/200) 4096 3576)/2 = (7045377:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3575
  · change cPayment 3576 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3576+point (1327/200) 4096 3577)/2)
    have hp : cPayment 3576 = (16976022822:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3576+point (1327/200) 4096 3577)/2 = (7046431:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3576
  · change cPayment 3577 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3577+point (1327/200) 4096 3578)/2)
    have hp : cPayment 3577 = (16942558201:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3577+point (1327/200) 4096 3578)/2 = (1409497:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3577
  · change cPayment 3578 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3578+point (1327/200) 4096 3579)/2)
    have hp : cPayment 3578 = (16909096146:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3578+point (1327/200) 4096 3579)/2 = (7048539:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3578
  · change cPayment 3579 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3579+point (1327/200) 4096 3580)/2)
    have hp : cPayment 3579 = (16875636659:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3579+point (1327/200) 4096 3580)/2 = (7049593:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3579
  · change cPayment 3580 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3580+point (1327/200) 4096 3581)/2)
    have hp : cPayment 3580 = (16842179744:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3580+point (1327/200) 4096 3581)/2 = (7050647:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3580
  · change cPayment 3581 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3581+point (1327/200) 4096 3582)/2)
    have hp : cPayment 3581 = (16808725404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3581+point (1327/200) 4096 3582)/2 = (7051701:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3581
  · change cPayment 3582 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3582+point (1327/200) 4096 3583)/2)
    have hp : cPayment 3582 = (16775273642:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3582+point (1327/200) 4096 3583)/2 = (1410551:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3582
  · change cPayment 3583 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3583+point (1327/200) 4096 3584)/2)
    have hp : cPayment 3583 = (16741824462:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3583+point (1327/200) 4096 3584)/2 = (7053809:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3583
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_223
