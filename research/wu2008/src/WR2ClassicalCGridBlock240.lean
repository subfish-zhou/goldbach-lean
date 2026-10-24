import WR2ClassicalCPayments
import WR2ClassicalCPoints240
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_240 (j : Fin 16) : cPayment (16*240+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*240+j.val)+point (1327/200) 4096 (16*240+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3840 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3840+point (1327/200) 4096 3841)/2)
    have hp : cPayment 3840 = (8239463247:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3840+point (1327/200) 4096 3841)/2 = (7324687:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3840
  · change cPayment 3841 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3841+point (1327/200) 4096 3842)/2)
    have hp : cPayment 3841 = (8206776163:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3841+point (1327/200) 4096 3842)/2 = (7325741:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3841
  · change cPayment 3842 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3842+point (1327/200) 4096 3843)/2)
    have hp : cPayment 3842 = (8174092359:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3842+point (1327/200) 4096 3843)/2 = (1465359:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3842
  · change cPayment 3843 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3843+point (1327/200) 4096 3844)/2)
    have hp : cPayment 3843 = (8141411838:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3843+point (1327/200) 4096 3844)/2 = (7327849:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3843
  · change cPayment 3844 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3844+point (1327/200) 4096 3845)/2)
    have hp : cPayment 3844 = (8108734601:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3844+point (1327/200) 4096 3845)/2 = (7328903:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3844
  · change cPayment 3845 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3845+point (1327/200) 4096 3846)/2)
    have hp : cPayment 3845 = (8076060650:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3845+point (1327/200) 4096 3846)/2 = (7329957:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3845
  · change cPayment 3846 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3846+point (1327/200) 4096 3847)/2)
    have hp : cPayment 3846 = (8043389988:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3846+point (1327/200) 4096 3847)/2 = (7331011:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3846
  · change cPayment 3847 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3847+point (1327/200) 4096 3848)/2)
    have hp : cPayment 3847 = (8010722617:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3847+point (1327/200) 4096 3848)/2 = (1466413:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3847
  · change cPayment 3848 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3848+point (1327/200) 4096 3849)/2)
    have hp : cPayment 3848 = (7978058539:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3848+point (1327/200) 4096 3849)/2 = (7333119:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3848
  · change cPayment 3849 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3849+point (1327/200) 4096 3850)/2)
    have hp : cPayment 3849 = (7945397757:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3849+point (1327/200) 4096 3850)/2 = (7334173:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3849
  · change cPayment 3850 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3850+point (1327/200) 4096 3851)/2)
    have hp : cPayment 3850 = (7912740272:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3850+point (1327/200) 4096 3851)/2 = (7335227:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3850
  · change cPayment 3851 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3851+point (1327/200) 4096 3852)/2)
    have hp : cPayment 3851 = (7880086087:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3851+point (1327/200) 4096 3852)/2 = (7336281:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3851
  · change cPayment 3852 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3852+point (1327/200) 4096 3853)/2)
    have hp : cPayment 3852 = (7847435203:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3852+point (1327/200) 4096 3853)/2 = (1467467:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3852
  · change cPayment 3853 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3853+point (1327/200) 4096 3854)/2)
    have hp : cPayment 3853 = (7814787623:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3853+point (1327/200) 4096 3854)/2 = (7338389:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3853
  · change cPayment 3854 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3854+point (1327/200) 4096 3855)/2)
    have hp : cPayment 3854 = (7782143350:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3854+point (1327/200) 4096 3855)/2 = (7339443:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3854
  · change cPayment 3855 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3855+point (1327/200) 4096 3856)/2)
    have hp : cPayment 3855 = (7749502384:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3855+point (1327/200) 4096 3856)/2 = (7340497:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3855
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_240
