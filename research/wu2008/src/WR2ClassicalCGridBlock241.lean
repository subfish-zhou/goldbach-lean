import WR2ClassicalCPayments
import WR2ClassicalCPoints241
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_241 (j : Fin 16) : cPayment (16*241+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*241+j.val)+point (1327/200) 4096 (16*241+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3856 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3856+point (1327/200) 4096 3857)/2)
    have hp : cPayment 3856 = (7716864730:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3856+point (1327/200) 4096 3857)/2 = (7341551:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3856
  · change cPayment 3857 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3857+point (1327/200) 4096 3858)/2)
    have hp : cPayment 3857 = (7684230387:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3857+point (1327/200) 4096 3858)/2 = (1468521:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3857
  · change cPayment 3858 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3858+point (1327/200) 4096 3859)/2)
    have hp : cPayment 3858 = (7651599359:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3858+point (1327/200) 4096 3859)/2 = (7343659:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3858
  · change cPayment 3859 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3859+point (1327/200) 4096 3860)/2)
    have hp : cPayment 3859 = (7618971649:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3859+point (1327/200) 4096 3860)/2 = (7344713:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3859
  · change cPayment 3860 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3860+point (1327/200) 4096 3861)/2)
    have hp : cPayment 3860 = (7586347257:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3860+point (1327/200) 4096 3861)/2 = (7345767:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3860
  · change cPayment 3861 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3861+point (1327/200) 4096 3862)/2)
    have hp : cPayment 3861 = (7553726186:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3861+point (1327/200) 4096 3862)/2 = (7346821:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3861
  · change cPayment 3862 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3862+point (1327/200) 4096 3863)/2)
    have hp : cPayment 3862 = (7521108438:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3862+point (1327/200) 4096 3863)/2 = (293915:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3862
  · change cPayment 3863 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3863+point (1327/200) 4096 3864)/2)
    have hp : cPayment 3863 = (7488494015:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3863+point (1327/200) 4096 3864)/2 = (7348929:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3863
  · change cPayment 3864 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3864+point (1327/200) 4096 3865)/2)
    have hp : cPayment 3864 = (7455882920:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3864+point (1327/200) 4096 3865)/2 = (7349983:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3864
  · change cPayment 3865 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3865+point (1327/200) 4096 3866)/2)
    have hp : cPayment 3865 = (7423275155:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3865+point (1327/200) 4096 3866)/2 = (7351037:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3865
  · change cPayment 3866 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3866+point (1327/200) 4096 3867)/2)
    have hp : cPayment 3866 = (7390670721:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3866+point (1327/200) 4096 3867)/2 = (7352091:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3866
  · change cPayment 3867 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3867+point (1327/200) 4096 3868)/2)
    have hp : cPayment 3867 = (7358069621:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3867+point (1327/200) 4096 3868)/2 = (1470629:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3867
  · change cPayment 3868 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3868+point (1327/200) 4096 3869)/2)
    have hp : cPayment 3868 = (7325471857:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3868+point (1327/200) 4096 3869)/2 = (7354199:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3868
  · change cPayment 3869 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3869+point (1327/200) 4096 3870)/2)
    have hp : cPayment 3869 = (7292877431:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3869+point (1327/200) 4096 3870)/2 = (7355253:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3869
  · change cPayment 3870 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3870+point (1327/200) 4096 3871)/2)
    have hp : cPayment 3870 = (7260286344:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3870+point (1327/200) 4096 3871)/2 = (7356307:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3870
  · change cPayment 3871 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3871+point (1327/200) 4096 3872)/2)
    have hp : cPayment 3871 = (7227698600:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3871+point (1327/200) 4096 3872)/2 = (7357361:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3871
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_241
