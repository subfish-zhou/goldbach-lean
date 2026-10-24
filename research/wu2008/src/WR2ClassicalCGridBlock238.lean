import WR2ClassicalCPayments
import WR2ClassicalCPoints238
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_238 (j : Fin 16) : cPayment (16*238+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*238+j.val)+point (1327/200) 4096 (16*238+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3808 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3808+point (1327/200) 4096 3809)/2)
    have hp : cPayment 3808 = (9287168507:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3808+point (1327/200) 4096 3809)/2 = (7290959:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3808
  · change cPayment 3809 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3809+point (1327/200) 4096 3810)/2)
    have hp : cPayment 3809 = (9254377639:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3809+point (1327/200) 4096 3810)/2 = (7292013:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3809
  · change cPayment 3810 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3810+point (1327/200) 4096 3811)/2)
    have hp : cPayment 3810 = (9221589979:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3810+point (1327/200) 4096 3811)/2 = (7293067:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3810
  · change cPayment 3811 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3811+point (1327/200) 4096 3812)/2)
    have hp : cPayment 3811 = (9188805530:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3811+point (1327/200) 4096 3812)/2 = (7294121:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3811
  · change cPayment 3812 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3812+point (1327/200) 4096 3813)/2)
    have hp : cPayment 3812 = (9156024293:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3812+point (1327/200) 4096 3813)/2 = (291807:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3812
  · change cPayment 3813 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3813+point (1327/200) 4096 3814)/2)
    have hp : cPayment 3813 = (9123246272:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3813+point (1327/200) 4096 3814)/2 = (7296229:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3813
  · change cPayment 3814 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3814+point (1327/200) 4096 3815)/2)
    have hp : cPayment 3814 = (9090471467:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3814+point (1327/200) 4096 3815)/2 = (7297283:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3814
  · change cPayment 3815 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3815+point (1327/200) 4096 3816)/2)
    have hp : cPayment 3815 = (9057699882:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3815+point (1327/200) 4096 3816)/2 = (7298337:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3815
  · change cPayment 3816 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3816+point (1327/200) 4096 3817)/2)
    have hp : cPayment 3816 = (9024931519:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3816+point (1327/200) 4096 3817)/2 = (7299391:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3816
  · change cPayment 3817 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3817+point (1327/200) 4096 3818)/2)
    have hp : cPayment 3817 = (8992166381:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3817+point (1327/200) 4096 3818)/2 = (1460089:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3817
  · change cPayment 3818 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3818+point (1327/200) 4096 3819)/2)
    have hp : cPayment 3818 = (8959404468:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3818+point (1327/200) 4096 3819)/2 = (7301499:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3818
  · change cPayment 3819 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3819+point (1327/200) 4096 3820)/2)
    have hp : cPayment 3819 = (8926645784:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3819+point (1327/200) 4096 3820)/2 = (7302553:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3819
  · change cPayment 3820 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3820+point (1327/200) 4096 3821)/2)
    have hp : cPayment 3820 = (8893890332:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3820+point (1327/200) 4096 3821)/2 = (7303607:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3820
  · change cPayment 3821 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3821+point (1327/200) 4096 3822)/2)
    have hp : cPayment 3821 = (8861138112:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3821+point (1327/200) 4096 3822)/2 = (7304661:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3821
  · change cPayment 3822 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3822+point (1327/200) 4096 3823)/2)
    have hp : cPayment 3822 = (8828389128:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3822+point (1327/200) 4096 3823)/2 = (1461143:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3822
  · change cPayment 3823 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3823+point (1327/200) 4096 3824)/2)
    have hp : cPayment 3823 = (8795643382:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3823+point (1327/200) 4096 3824)/2 = (7306769:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3823
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_238
