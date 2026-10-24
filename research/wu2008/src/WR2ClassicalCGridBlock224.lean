import WR2ClassicalCPayments
import WR2ClassicalCPoints224
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_224 (j : Fin 16) : cPayment (16*224+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*224+j.val)+point (1327/200) 4096 (16*224+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3584 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3584+point (1327/200) 4096 3585)/2)
    have hp : cPayment 3584 = (16708377867:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3584+point (1327/200) 4096 3585)/2 = (7054863:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3584
  · change cPayment 3585 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3585+point (1327/200) 4096 3586)/2)
    have hp : cPayment 3585 = (16674933860:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3585+point (1327/200) 4096 3586)/2 = (7055917:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3585
  · change cPayment 3586 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3586+point (1327/200) 4096 3587)/2)
    have hp : cPayment 3586 = (16641492444:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3586+point (1327/200) 4096 3587)/2 = (7056971:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3586
  · change cPayment 3587 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3587+point (1327/200) 4096 3588)/2)
    have hp : cPayment 3587 = (16608053623:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3587+point (1327/200) 4096 3588)/2 = (282321:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3587
  · change cPayment 3588 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3588+point (1327/200) 4096 3589)/2)
    have hp : cPayment 3588 = (16574617400:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3588+point (1327/200) 4096 3589)/2 = (7059079:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3588
  · change cPayment 3589 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3589+point (1327/200) 4096 3590)/2)
    have hp : cPayment 3589 = (16541183778:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3589+point (1327/200) 4096 3590)/2 = (7060133:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3589
  · change cPayment 3590 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3590+point (1327/200) 4096 3591)/2)
    have hp : cPayment 3590 = (16507752760:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3590+point (1327/200) 4096 3591)/2 = (7061187:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3590
  · change cPayment 3591 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3591+point (1327/200) 4096 3592)/2)
    have hp : cPayment 3591 = (16474324349:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3591+point (1327/200) 4096 3592)/2 = (7062241:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3591
  · change cPayment 3592 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3592+point (1327/200) 4096 3593)/2)
    have hp : cPayment 3592 = (16440898549:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3592+point (1327/200) 4096 3593)/2 = (1412659:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3592
  · change cPayment 3593 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3593+point (1327/200) 4096 3594)/2)
    have hp : cPayment 3593 = (16407475363:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3593+point (1327/200) 4096 3594)/2 = (7064349:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3593
  · change cPayment 3594 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3594+point (1327/200) 4096 3595)/2)
    have hp : cPayment 3594 = (16374054795:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3594+point (1327/200) 4096 3595)/2 = (7065403:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3594
  · change cPayment 3595 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3595+point (1327/200) 4096 3596)/2)
    have hp : cPayment 3595 = (16340636846:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3595+point (1327/200) 4096 3596)/2 = (7066457:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3595
  · change cPayment 3596 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3596+point (1327/200) 4096 3597)/2)
    have hp : cPayment 3596 = (16307221521:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3596+point (1327/200) 4096 3597)/2 = (7067511:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3596
  · change cPayment 3597 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3597+point (1327/200) 4096 3598)/2)
    have hp : cPayment 3597 = (16273808823:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3597+point (1327/200) 4096 3598)/2 = (1413713:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3597
  · change cPayment 3598 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3598+point (1327/200) 4096 3599)/2)
    have hp : cPayment 3598 = (16240398755:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3598+point (1327/200) 4096 3599)/2 = (7069619:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3598
  · change cPayment 3599 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3599+point (1327/200) 4096 3600)/2)
    have hp : cPayment 3599 = (16206991320:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3599+point (1327/200) 4096 3600)/2 = (7070673:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3599
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_224
