import WR2ClassicalCPayments
import WR2ClassicalCPoints228
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_228 (j : Fin 16) : cPayment (16*228+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*228+j.val)+point (1327/200) 4096 (16*228+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3648 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3648+point (1327/200) 4096 3649)/2)
    have hp : cPayment 3648 = (14573317574:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3648+point (1327/200) 4096 3649)/2 = (7122319:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3648
  · change cPayment 3649 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3649+point (1327/200) 4096 3650)/2)
    have hp : cPayment 3649 = (14540045751:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3649+point (1327/200) 4096 3650)/2 = (7123373:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3649
  · change cPayment 3650 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3650+point (1327/200) 4096 3651)/2)
    have hp : cPayment 3650 = (14506776716:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3650+point (1327/200) 4096 3651)/2 = (7124427:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3650
  · change cPayment 3651 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3651+point (1327/200) 4096 3652)/2)
    have hp : cPayment 3651 = (14473510474:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3651+point (1327/200) 4096 3652)/2 = (7125481:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3651
  · change cPayment 3652 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3652+point (1327/200) 4096 3653)/2)
    have hp : cPayment 3652 = (14440247027:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3652+point (1327/200) 4096 3653)/2 = (1425307:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3652
  · change cPayment 3653 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3653+point (1327/200) 4096 3654)/2)
    have hp : cPayment 3653 = (14406986378:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3653+point (1327/200) 4096 3654)/2 = (7127589:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3653
  · change cPayment 3654 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3654+point (1327/200) 4096 3655)/2)
    have hp : cPayment 3654 = (14373728531:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3654+point (1327/200) 4096 3655)/2 = (7128643:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3654
  · change cPayment 3655 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3655+point (1327/200) 4096 3656)/2)
    have hp : cPayment 3655 = (14340473487:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3655+point (1327/200) 4096 3656)/2 = (7129697:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3655
  · change cPayment 3656 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3656+point (1327/200) 4096 3657)/2)
    have hp : cPayment 3656 = (14307221251:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3656+point (1327/200) 4096 3657)/2 = (7130751:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3656
  · change cPayment 3657 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3657+point (1327/200) 4096 3658)/2)
    have hp : cPayment 3657 = (14273971824:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3657+point (1327/200) 4096 3658)/2 = (1426361:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3657
  · change cPayment 3658 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3658+point (1327/200) 4096 3659)/2)
    have hp : cPayment 3658 = (14240725210:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3658+point (1327/200) 4096 3659)/2 = (7132859:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3658
  · change cPayment 3659 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3659+point (1327/200) 4096 3660)/2)
    have hp : cPayment 3659 = (14207481412:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3659+point (1327/200) 4096 3660)/2 = (7133913:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3659
  · change cPayment 3660 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3660+point (1327/200) 4096 3661)/2)
    have hp : cPayment 3660 = (14174240432:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3660+point (1327/200) 4096 3661)/2 = (7134967:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3660
  · change cPayment 3661 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3661+point (1327/200) 4096 3662)/2)
    have hp : cPayment 3661 = (14141002274:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3661+point (1327/200) 4096 3662)/2 = (7136021:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3661
  · change cPayment 3662 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3662+point (1327/200) 4096 3663)/2)
    have hp : cPayment 3662 = (14107766940:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3662+point (1327/200) 4096 3663)/2 = (285483:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3662
  · change cPayment 3663 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3663+point (1327/200) 4096 3664)/2)
    have hp : cPayment 3663 = (14074534434:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3663+point (1327/200) 4096 3664)/2 = (7138129:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3663
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_228
