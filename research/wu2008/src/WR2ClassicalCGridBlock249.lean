import WR2ClassicalCPayments
import WR2ClassicalCPoints249
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_249 (j : Fin 16) : cPayment (16*249+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*249+j.val)+point (1327/200) 4096 (16*249+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3984 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3984+point (1327/200) 4096 3985)/2)
    have hp : cPayment 3984 = (3567303647:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3984+point (1327/200) 4096 3985)/2 = (7476463:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3984
  · change cPayment 3985 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3985+point (1327/200) 4096 3986)/2)
    have hp : cPayment 3985 = (3535109802:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3985+point (1327/200) 4096 3986)/2 = (7477517:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3985
  · change cPayment 3986 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3986+point (1327/200) 4096 3987)/2)
    have hp : cPayment 3986 = (3502919519:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3986+point (1327/200) 4096 3987)/2 = (7478571:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3986
  · change cPayment 3987 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3987+point (1327/200) 4096 3988)/2)
    have hp : cPayment 3987 = (3470732799:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3987+point (1327/200) 4096 3988)/2 = (299185:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3987
  · change cPayment 3988 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3988+point (1327/200) 4096 3989)/2)
    have hp : cPayment 3988 = (3438549643:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3988+point (1327/200) 4096 3989)/2 = (7480679:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3988
  · change cPayment 3989 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3989+point (1327/200) 4096 3990)/2)
    have hp : cPayment 3989 = (3406370055:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3989+point (1327/200) 4096 3990)/2 = (7481733:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3989
  · change cPayment 3990 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3990+point (1327/200) 4096 3991)/2)
    have hp : cPayment 3990 = (3374194034:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3990+point (1327/200) 4096 3991)/2 = (7482787:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3990
  · change cPayment 3991 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3991+point (1327/200) 4096 3992)/2)
    have hp : cPayment 3991 = (3342021583:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3991+point (1327/200) 4096 3992)/2 = (7483841:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3991
  · change cPayment 3992 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3992+point (1327/200) 4096 3993)/2)
    have hp : cPayment 3992 = (3309852704:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3992+point (1327/200) 4096 3993)/2 = (1496979:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3992
  · change cPayment 3993 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3993+point (1327/200) 4096 3994)/2)
    have hp : cPayment 3993 = (3277687399:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3993+point (1327/200) 4096 3994)/2 = (7485949:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3993
  · change cPayment 3994 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3994+point (1327/200) 4096 3995)/2)
    have hp : cPayment 3994 = (3245525668:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3994+point (1327/200) 4096 3995)/2 = (7487003:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3994
  · change cPayment 3995 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3995+point (1327/200) 4096 3996)/2)
    have hp : cPayment 3995 = (3213367514:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3995+point (1327/200) 4096 3996)/2 = (7488057:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3995
  · change cPayment 3996 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3996+point (1327/200) 4096 3997)/2)
    have hp : cPayment 3996 = (3181212939:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3996+point (1327/200) 4096 3997)/2 = (7489111:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3996
  · change cPayment 3997 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3997+point (1327/200) 4096 3998)/2)
    have hp : cPayment 3997 = (3149061944:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3997+point (1327/200) 4096 3998)/2 = (1498033:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3997
  · change cPayment 3998 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3998+point (1327/200) 4096 3999)/2)
    have hp : cPayment 3998 = (3116914530:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3998+point (1327/200) 4096 3999)/2 = (7491219:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3998
  · change cPayment 3999 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3999+point (1327/200) 4096 4000)/2)
    have hp : cPayment 3999 = (3084770701:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3999+point (1327/200) 4096 4000)/2 = (7492273:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3999
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_249
