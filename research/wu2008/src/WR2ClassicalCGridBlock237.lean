import WR2ClassicalCPayments
import WR2ClassicalCPoints237
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_237 (j : Fin 16) : cPayment (16*237+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*237+j.val)+point (1327/200) 4096 (16*237+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3792 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3792+point (1327/200) 4096 3793)/2)
    have hp : cPayment 3792 = (9812256798:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3792+point (1327/200) 4096 3793)/2 = (1454819:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3792
  · change cPayment 3793 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3793+point (1327/200) 4096 3794)/2)
    have hp : cPayment 3793 = (9779414917:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3793+point (1327/200) 4096 3794)/2 = (7275149:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3793
  · change cPayment 3794 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3794+point (1327/200) 4096 3795)/2)
    have hp : cPayment 3794 = (9746576207:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3794+point (1327/200) 4096 3795)/2 = (7276203:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3794
  · change cPayment 3795 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3795+point (1327/200) 4096 3796)/2)
    have hp : cPayment 3795 = (9713740670:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3795+point (1327/200) 4096 3796)/2 = (7277257:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3795
  · change cPayment 3796 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3796+point (1327/200) 4096 3797)/2)
    have hp : cPayment 3796 = (9680908308:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3796+point (1327/200) 4096 3797)/2 = (7278311:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3796
  · change cPayment 3797 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3797+point (1327/200) 4096 3798)/2)
    have hp : cPayment 3797 = (9648079125:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3797+point (1327/200) 4096 3798)/2 = (1455873:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3797
  · change cPayment 3798 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3798+point (1327/200) 4096 3799)/2)
    have hp : cPayment 3798 = (9615253121:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3798+point (1327/200) 4096 3799)/2 = (7280419:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3798
  · change cPayment 3799 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3799+point (1327/200) 4096 3800)/2)
    have hp : cPayment 3799 = (9582430300:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3799+point (1327/200) 4096 3800)/2 = (7281473:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3799
  · change cPayment 3800 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3800+point (1327/200) 4096 3801)/2)
    have hp : cPayment 3800 = (9549610663:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3800+point (1327/200) 4096 3801)/2 = (7282527:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3800
  · change cPayment 3801 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3801+point (1327/200) 4096 3802)/2)
    have hp : cPayment 3801 = (9516794214:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3801+point (1327/200) 4096 3802)/2 = (7283581:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3801
  · change cPayment 3802 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3802+point (1327/200) 4096 3803)/2)
    have hp : cPayment 3802 = (9483980954:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3802+point (1327/200) 4096 3803)/2 = (1456927:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3802
  · change cPayment 3803 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3803+point (1327/200) 4096 3804)/2)
    have hp : cPayment 3803 = (9451170887:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3803+point (1327/200) 4096 3804)/2 = (7285689:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3803
  · change cPayment 3804 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3804+point (1327/200) 4096 3805)/2)
    have hp : cPayment 3804 = (9418364013:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3804+point (1327/200) 4096 3805)/2 = (7286743:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3804
  · change cPayment 3805 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3805+point (1327/200) 4096 3806)/2)
    have hp : cPayment 3805 = (9385560336:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3805+point (1327/200) 4096 3806)/2 = (7287797:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3805
  · change cPayment 3806 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3806+point (1327/200) 4096 3807)/2)
    have hp : cPayment 3806 = (9352759858:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3806+point (1327/200) 4096 3807)/2 = (7288851:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3806
  · change cPayment 3807 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3807+point (1327/200) 4096 3808)/2)
    have hp : cPayment 3807 = (9319962581:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3807+point (1327/200) 4096 3808)/2 = (1457981:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3807
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_237
