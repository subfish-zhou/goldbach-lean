import WR2ClassicalCPayments
import WR2ClassicalCPoints221
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_221 (j : Fin 16) : cPayment (16*221+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*221+j.val)+point (1327/200) 4096 (16*221+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3536 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3536+point (1327/200) 4096 3537)/2)
    have hp : cPayment 3536 = (18316672899:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3536+point (1327/200) 4096 3537)/2 = (7004271:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3536
  · change cPayment 3537 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3537+point (1327/200) 4096 3538)/2)
    have hp : cPayment 3537 = (18283108413:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3537+point (1327/200) 4096 3538)/2 = (280213:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3537
  · change cPayment 3538 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3538+point (1327/200) 4096 3539)/2)
    have hp : cPayment 3538 = (18249546358:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3538+point (1327/200) 4096 3539)/2 = (7006379:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3538
  · change cPayment 3539 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3539+point (1327/200) 4096 3540)/2)
    have hp : cPayment 3539 = (18215986736:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3539+point (1327/200) 4096 3540)/2 = (7007433:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3539
  · change cPayment 3540 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3540+point (1327/200) 4096 3541)/2)
    have hp : cPayment 3540 = (18182429551:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3540+point (1327/200) 4096 3541)/2 = (7008487:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3540
  · change cPayment 3541 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3541+point (1327/200) 4096 3542)/2)
    have hp : cPayment 3541 = (18148874807:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3541+point (1327/200) 4096 3542)/2 = (7009541:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3541
  · change cPayment 3542 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3542+point (1327/200) 4096 3543)/2)
    have hp : cPayment 3542 = (18115322506:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3542+point (1327/200) 4096 3543)/2 = (1402119:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3542
  · change cPayment 3543 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3543+point (1327/200) 4096 3544)/2)
    have hp : cPayment 3543 = (18081772653:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3543+point (1327/200) 4096 3544)/2 = (7011649:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3543
  · change cPayment 3544 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3544+point (1327/200) 4096 3545)/2)
    have hp : cPayment 3544 = (18048225251:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3544+point (1327/200) 4096 3545)/2 = (7012703:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3544
  · change cPayment 3545 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3545+point (1327/200) 4096 3546)/2)
    have hp : cPayment 3545 = (18014680303:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3545+point (1327/200) 4096 3546)/2 = (7013757:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3545
  · change cPayment 3546 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3546+point (1327/200) 4096 3547)/2)
    have hp : cPayment 3546 = (17981137813:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3546+point (1327/200) 4096 3547)/2 = (7014811:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3546
  · change cPayment 3547 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3547+point (1327/200) 4096 3548)/2)
    have hp : cPayment 3547 = (17947597784:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3547+point (1327/200) 4096 3548)/2 = (1403173:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3547
  · change cPayment 3548 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3548+point (1327/200) 4096 3549)/2)
    have hp : cPayment 3548 = (17914060220:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3548+point (1327/200) 4096 3549)/2 = (7016919:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3548
  · change cPayment 3549 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3549+point (1327/200) 4096 3550)/2)
    have hp : cPayment 3549 = (17880525123:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3549+point (1327/200) 4096 3550)/2 = (7017973:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3549
  · change cPayment 3550 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3550+point (1327/200) 4096 3551)/2)
    have hp : cPayment 3550 = (17846992498:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3550+point (1327/200) 4096 3551)/2 = (7019027:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3550
  · change cPayment 3551 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3551+point (1327/200) 4096 3552)/2)
    have hp : cPayment 3551 = (17813462348:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3551+point (1327/200) 4096 3552)/2 = (7020081:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3551
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_221
