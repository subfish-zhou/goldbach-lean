import WR2ClassicalCPayments
import WR2ClassicalCPoints217
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_217 (j : Fin 16) : cPayment (16*217+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*217+j.val)+point (1327/200) 4096 (16*217+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3472 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3472+point (1327/200) 4096 3473)/2)
    have hp : cPayment 3472 = (20469691500:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3472+point (1327/200) 4096 3473)/2 = (1387363:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3472
  · change cPayment 3473 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3473+point (1327/200) 4096 3474)/2)
    have hp : cPayment 3473 = (20435978957:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3473+point (1327/200) 4096 3474)/2 = (6937869:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3473
  · change cPayment 3474 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3474+point (1327/200) 4096 3475)/2)
    have hp : cPayment 3474 = (20402268611:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3474+point (1327/200) 4096 3475)/2 = (6938923:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3474
  · change cPayment 3475 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3475+point (1327/200) 4096 3476)/2)
    have hp : cPayment 3475 = (20368560465:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3475+point (1327/200) 4096 3476)/2 = (6939977:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3475
  · change cPayment 3476 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3476+point (1327/200) 4096 3477)/2)
    have hp : cPayment 3476 = (20334854524:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3476+point (1327/200) 4096 3477)/2 = (6941031:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3476
  · change cPayment 3477 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3477+point (1327/200) 4096 3478)/2)
    have hp : cPayment 3477 = (20301150791:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3477+point (1327/200) 4096 3478)/2 = (1388417:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3477
  · change cPayment 3478 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3478+point (1327/200) 4096 3479)/2)
    have hp : cPayment 3478 = (20267449270:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3478+point (1327/200) 4096 3479)/2 = (6943139:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3478
  · change cPayment 3479 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3479+point (1327/200) 4096 3480)/2)
    have hp : cPayment 3479 = (20233749965:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3479+point (1327/200) 4096 3480)/2 = (6944193:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3479
  · change cPayment 3480 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3480+point (1327/200) 4096 3481)/2)
    have hp : cPayment 3480 = (20200052879:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3480+point (1327/200) 4096 3481)/2 = (6945247:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3480
  · change cPayment 3481 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3481+point (1327/200) 4096 3482)/2)
    have hp : cPayment 3481 = (20166358016:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3481+point (1327/200) 4096 3482)/2 = (6946301:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3481
  · change cPayment 3482 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3482+point (1327/200) 4096 3483)/2)
    have hp : cPayment 3482 = (20132665381:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3482+point (1327/200) 4096 3483)/2 = (1389471:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3482
  · change cPayment 3483 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3483+point (1327/200) 4096 3484)/2)
    have hp : cPayment 3483 = (20098974977:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3483+point (1327/200) 4096 3484)/2 = (6948409:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3483
  · change cPayment 3484 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3484+point (1327/200) 4096 3485)/2)
    have hp : cPayment 3484 = (20065286807:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3484+point (1327/200) 4096 3485)/2 = (6949463:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3484
  · change cPayment 3485 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3485+point (1327/200) 4096 3486)/2)
    have hp : cPayment 3485 = (20031600876:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3485+point (1327/200) 4096 3486)/2 = (6950517:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3485
  · change cPayment 3486 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3486+point (1327/200) 4096 3487)/2)
    have hp : cPayment 3486 = (19997917187:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3486+point (1327/200) 4096 3487)/2 = (6951571:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3486
  · change cPayment 3487 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3487+point (1327/200) 4096 3488)/2)
    have hp : cPayment 3487 = (19964235744:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3487+point (1327/200) 4096 3488)/2 = (278105:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3487
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_217
