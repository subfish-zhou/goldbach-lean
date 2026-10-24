import WR2ClassicalCPayments
import WR2ClassicalCPoints227
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_227 (j : Fin 16) : cPayment (16*227+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*227+j.val)+point (1327/200) 4096 (16*227+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3632 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3632+point (1327/200) 4096 3633)/2)
    have hp : cPayment 3632 = (15106043685:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3632+point (1327/200) 4096 3633)/2 = (1421091:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3632
  · change cPayment 3633 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3633+point (1327/200) 4096 3634)/2)
    have hp : cPayment 3633 = (15072727636:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3633+point (1327/200) 4096 3634)/2 = (7106509:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3633
  · change cPayment 3634 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3634+point (1327/200) 4096 3635)/2)
    have hp : cPayment 3634 = (15039414329:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3634+point (1327/200) 4096 3635)/2 = (7107563:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3634
  · change cPayment 3635 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3635+point (1327/200) 4096 3636)/2)
    have hp : cPayment 3635 = (15006103766:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3635+point (1327/200) 4096 3636)/2 = (7108617:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3635
  · change cPayment 3636 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3636+point (1327/200) 4096 3637)/2)
    have hp : cPayment 3636 = (14972795951:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3636+point (1327/200) 4096 3637)/2 = (7109671:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3636
  · change cPayment 3637 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3637+point (1327/200) 4096 3638)/2)
    have hp : cPayment 3637 = (14939490886:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3637+point (1327/200) 4096 3638)/2 = (284429:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3637
  · change cPayment 3638 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3638+point (1327/200) 4096 3639)/2)
    have hp : cPayment 3638 = (14906188575:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3638+point (1327/200) 4096 3639)/2 = (7111779:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3638
  · change cPayment 3639 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3639+point (1327/200) 4096 3640)/2)
    have hp : cPayment 3639 = (14872889021:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3639+point (1327/200) 4096 3640)/2 = (7112833:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3639
  · change cPayment 3640 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3640+point (1327/200) 4096 3641)/2)
    have hp : cPayment 3640 = (14839592226:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3640+point (1327/200) 4096 3641)/2 = (7113887:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3640
  · change cPayment 3641 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3641+point (1327/200) 4096 3642)/2)
    have hp : cPayment 3641 = (14806298194:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3641+point (1327/200) 4096 3642)/2 = (7114941:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3641
  · change cPayment 3642 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3642+point (1327/200) 4096 3643)/2)
    have hp : cPayment 3642 = (14773006928:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3642+point (1327/200) 4096 3643)/2 = (1423199:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3642
  · change cPayment 3643 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3643+point (1327/200) 4096 3644)/2)
    have hp : cPayment 3643 = (14739718430:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3643+point (1327/200) 4096 3644)/2 = (7117049:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3643
  · change cPayment 3644 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3644+point (1327/200) 4096 3645)/2)
    have hp : cPayment 3644 = (14706432704:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3644+point (1327/200) 4096 3645)/2 = (7118103:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3644
  · change cPayment 3645 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3645+point (1327/200) 4096 3646)/2)
    have hp : cPayment 3645 = (14673149752:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3645+point (1327/200) 4096 3646)/2 = (7119157:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3645
  · change cPayment 3646 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3646+point (1327/200) 4096 3647)/2)
    have hp : cPayment 3646 = (14639869578:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3646+point (1327/200) 4096 3647)/2 = (7120211:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3646
  · change cPayment 3647 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3647+point (1327/200) 4096 3648)/2)
    have hp : cPayment 3647 = (14606592185:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3647+point (1327/200) 4096 3648)/2 = (1424253:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3647
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_227
