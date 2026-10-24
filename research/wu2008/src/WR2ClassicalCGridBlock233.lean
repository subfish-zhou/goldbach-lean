import WR2ClassicalCPayments
import WR2ClassicalCPoints233
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_233 (j : Fin 16) : cPayment (16*233+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*233+j.val)+point (1327/200) 4096 (16*233+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3728 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3728+point (1327/200) 4096 3729)/2)
    have hp : cPayment 3728 = (11920621256:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3728+point (1327/200) 4096 3729)/2 = (7206639:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3728
  · change cPayment 3729 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3729+point (1327/200) 4096 3730)/2)
    have hp : cPayment 3729 = (11887581538:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3729+point (1327/200) 4096 3730)/2 = (7207693:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3729
  · change cPayment 3730 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3730+point (1327/200) 4096 3731)/2)
    have hp : cPayment 3730 = (11854544830:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3730+point (1327/200) 4096 3731)/2 = (7208747:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3730
  · change cPayment 3731 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3731+point (1327/200) 4096 3732)/2)
    have hp : cPayment 3731 = (11821511137:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3731+point (1327/200) 4096 3732)/2 = (7209801:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3731
  · change cPayment 3732 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3732+point (1327/200) 4096 3733)/2)
    have hp : cPayment 3732 = (11788480461:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3732+point (1327/200) 4096 3733)/2 = (1442171:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3732
  · change cPayment 3733 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3733+point (1327/200) 4096 3734)/2)
    have hp : cPayment 3733 = (11755452804:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3733+point (1327/200) 4096 3734)/2 = (7211909:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3733
  · change cPayment 3734 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3734+point (1327/200) 4096 3735)/2)
    have hp : cPayment 3734 = (11722428169:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3734+point (1327/200) 4096 3735)/2 = (7212963:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3734
  · change cPayment 3735 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3735+point (1327/200) 4096 3736)/2)
    have hp : cPayment 3735 = (11689406559:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3735+point (1327/200) 4096 3736)/2 = (7214017:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3735
  · change cPayment 3736 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3736+point (1327/200) 4096 3737)/2)
    have hp : cPayment 3736 = (11656387976:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3736+point (1327/200) 4096 3737)/2 = (7215071:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3736
  · change cPayment 3737 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3737+point (1327/200) 4096 3738)/2)
    have hp : cPayment 3737 = (11623372422:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3737+point (1327/200) 4096 3738)/2 = (288645:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3737
  · change cPayment 3738 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3738+point (1327/200) 4096 3739)/2)
    have hp : cPayment 3738 = (11590359901:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3738+point (1327/200) 4096 3739)/2 = (7217179:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3738
  · change cPayment 3739 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3739+point (1327/200) 4096 3740)/2)
    have hp : cPayment 3739 = (11557350415:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3739+point (1327/200) 4096 3740)/2 = (7218233:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3739
  · change cPayment 3740 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3740+point (1327/200) 4096 3741)/2)
    have hp : cPayment 3740 = (11524343966:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3740+point (1327/200) 4096 3741)/2 = (7219287:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3740
  · change cPayment 3741 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3741+point (1327/200) 4096 3742)/2)
    have hp : cPayment 3741 = (11491340558:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3741+point (1327/200) 4096 3742)/2 = (7220341:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3741
  · change cPayment 3742 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3742+point (1327/200) 4096 3743)/2)
    have hp : cPayment 3742 = (11458340192:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3742+point (1327/200) 4096 3743)/2 = (1444279:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3742
  · change cPayment 3743 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3743+point (1327/200) 4096 3744)/2)
    have hp : cPayment 3743 = (11425342871:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3743+point (1327/200) 4096 3744)/2 = (7222449:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3743
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_233
