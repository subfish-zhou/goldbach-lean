import WR2ClassicalCPayments
import WR2ClassicalCPoints246
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_246 (j : Fin 16) : cPayment (16*246+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*246+j.val)+point (1327/200) 4096 (16*246+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3936 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3936+point (1327/200) 4096 3937)/2)
    have hp : cPayment 3936 = (5116761731:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3936+point (1327/200) 4096 3937)/2 = (7425871:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3936
  · change cPayment 3937 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3937+point (1327/200) 4096 3938)/2)
    have hp : cPayment 3937 = (5084399031:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3937+point (1327/200) 4096 3938)/2 = (297077:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3937
  · change cPayment 3938 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3938+point (1327/200) 4096 3939)/2)
    have hp : cPayment 3938 = (5052039807:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3938+point (1327/200) 4096 3939)/2 = (7427979:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3938
  · change cPayment 3939 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3939+point (1327/200) 4096 3940)/2)
    have hp : cPayment 3939 = (5019684059:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3939+point (1327/200) 4096 3940)/2 = (7429033:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3939
  · change cPayment 3940 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3940+point (1327/200) 4096 3941)/2)
    have hp : cPayment 3940 = (4987331790:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3940+point (1327/200) 4096 3941)/2 = (7430087:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3940
  · change cPayment 3941 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3941+point (1327/200) 4096 3942)/2)
    have hp : cPayment 3941 = (4954983001:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3941+point (1327/200) 4096 3942)/2 = (7431141:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3941
  · change cPayment 3942 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3942+point (1327/200) 4096 3943)/2)
    have hp : cPayment 3942 = (4922637695:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3942+point (1327/200) 4096 3943)/2 = (1486439:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3942
  · change cPayment 3943 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3943+point (1327/200) 4096 3944)/2)
    have hp : cPayment 3943 = (4890295873:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3943+point (1327/200) 4096 3944)/2 = (7433249:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3943
  · change cPayment 3944 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3944+point (1327/200) 4096 3945)/2)
    have hp : cPayment 3944 = (4857957537:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3944+point (1327/200) 4096 3945)/2 = (7434303:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3944
  · change cPayment 3945 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3945+point (1327/200) 4096 3946)/2)
    have hp : cPayment 3945 = (4825622689:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3945+point (1327/200) 4096 3946)/2 = (7435357:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3945
  · change cPayment 3946 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3946+point (1327/200) 4096 3947)/2)
    have hp : cPayment 3946 = (4793291331:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3946+point (1327/200) 4096 3947)/2 = (7436411:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3946
  · change cPayment 3947 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3947+point (1327/200) 4096 3948)/2)
    have hp : cPayment 3947 = (4760963465:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3947+point (1327/200) 4096 3948)/2 = (1487493:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3947
  · change cPayment 3948 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3948+point (1327/200) 4096 3949)/2)
    have hp : cPayment 3948 = (4728639092:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3948+point (1327/200) 4096 3949)/2 = (7438519:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3948
  · change cPayment 3949 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3949+point (1327/200) 4096 3950)/2)
    have hp : cPayment 3949 = (4696318214:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3949+point (1327/200) 4096 3950)/2 = (7439573:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3949
  · change cPayment 3950 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3950+point (1327/200) 4096 3951)/2)
    have hp : cPayment 3950 = (4664000834:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3950+point (1327/200) 4096 3951)/2 = (7440627:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3950
  · change cPayment 3951 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3951+point (1327/200) 4096 3952)/2)
    have hp : cPayment 3951 = (4631686953:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3951+point (1327/200) 4096 3952)/2 = (7441681:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3951
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_246
