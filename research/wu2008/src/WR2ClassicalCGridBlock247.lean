import WR2ClassicalCPayments
import WR2ClassicalCPoints247
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_247 (j : Fin 16) : cPayment (16*247+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*247+j.val)+point (1327/200) 4096 (16*247+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3952 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3952+point (1327/200) 4096 3953)/2)
    have hp : cPayment 3952 = (4599376572:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3952+point (1327/200) 4096 3953)/2 = (1488547:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3952
  · change cPayment 3953 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3953+point (1327/200) 4096 3954)/2)
    have hp : cPayment 3953 = (4567069694:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3953+point (1327/200) 4096 3954)/2 = (7443789:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3953
  · change cPayment 3954 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3954+point (1327/200) 4096 3955)/2)
    have hp : cPayment 3954 = (4534766321:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3954+point (1327/200) 4096 3955)/2 = (7444843:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3954
  · change cPayment 3955 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3955+point (1327/200) 4096 3956)/2)
    have hp : cPayment 3955 = (4502466454:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3955+point (1327/200) 4096 3956)/2 = (7445897:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3955
  · change cPayment 3956 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3956+point (1327/200) 4096 3957)/2)
    have hp : cPayment 3956 = (4470170095:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3956+point (1327/200) 4096 3957)/2 = (7446951:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3956
  · change cPayment 3957 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3957+point (1327/200) 4096 3958)/2)
    have hp : cPayment 3957 = (4437877246:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3957+point (1327/200) 4096 3958)/2 = (1489601:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3957
  · change cPayment 3958 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3958+point (1327/200) 4096 3959)/2)
    have hp : cPayment 3958 = (4405587909:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3958+point (1327/200) 4096 3959)/2 = (7449059:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3958
  · change cPayment 3959 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3959+point (1327/200) 4096 3960)/2)
    have hp : cPayment 3959 = (4373302085:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3959+point (1327/200) 4096 3960)/2 = (7450113:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3959
  · change cPayment 3960 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3960+point (1327/200) 4096 3961)/2)
    have hp : cPayment 3960 = (4341019777:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3960+point (1327/200) 4096 3961)/2 = (7451167:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3960
  · change cPayment 3961 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3961+point (1327/200) 4096 3962)/2)
    have hp : cPayment 3961 = (4308740986:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3961+point (1327/200) 4096 3962)/2 = (7452221:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3961
  · change cPayment 3962 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3962+point (1327/200) 4096 3963)/2)
    have hp : cPayment 3962 = (4276465714:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3962+point (1327/200) 4096 3963)/2 = (298131:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3962
  · change cPayment 3963 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3963+point (1327/200) 4096 3964)/2)
    have hp : cPayment 3963 = (4244193963:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3963+point (1327/200) 4096 3964)/2 = (7454329:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3963
  · change cPayment 3964 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3964+point (1327/200) 4096 3965)/2)
    have hp : cPayment 3964 = (4211925734:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3964+point (1327/200) 4096 3965)/2 = (7455383:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3964
  · change cPayment 3965 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3965+point (1327/200) 4096 3966)/2)
    have hp : cPayment 3965 = (4179661030:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3965+point (1327/200) 4096 3966)/2 = (7456437:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3965
  · change cPayment 3966 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3966+point (1327/200) 4096 3967)/2)
    have hp : cPayment 3966 = (4147399852:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3966+point (1327/200) 4096 3967)/2 = (7457491:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3966
  · change cPayment 3967 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3967+point (1327/200) 4096 3968)/2)
    have hp : cPayment 3967 = (4115142202:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3967+point (1327/200) 4096 3968)/2 = (1491709:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3967
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_247
