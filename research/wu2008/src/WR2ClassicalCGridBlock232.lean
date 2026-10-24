import WR2ClassicalCPayments
import WR2ClassicalCPoints232
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_232 (j : Fin 16) : cPayment (16*232+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*232+j.val)+point (1327/200) 4096 (16*232+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3712 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3712+point (1327/200) 4096 3713)/2)
    have hp : cPayment 3712 = (12449664184:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3712+point (1327/200) 4096 3713)/2 = (287591:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3712
  · change cPayment 3713 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3713+point (1327/200) 4096 3714)/2)
    have hp : cPayment 3713 = (12416576639:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3713+point (1327/200) 4096 3714)/2 = (7190829:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3713
  · change cPayment 3714 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3714+point (1327/200) 4096 3715)/2)
    have hp : cPayment 3714 = (12383492062:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3714+point (1327/200) 4096 3715)/2 = (7191883:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3714
  · change cPayment 3715 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3715+point (1327/200) 4096 3716)/2)
    have hp : cPayment 3715 = (12350410458:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3715+point (1327/200) 4096 3716)/2 = (7192937:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3715
  · change cPayment 3716 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3716+point (1327/200) 4096 3717)/2)
    have hp : cPayment 3716 = (12317331828:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3716+point (1327/200) 4096 3717)/2 = (7193991:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3716
  · change cPayment 3717 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3717+point (1327/200) 4096 3718)/2)
    have hp : cPayment 3717 = (12284256176:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3717+point (1327/200) 4096 3718)/2 = (1439009:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3717
  · change cPayment 3718 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3718+point (1327/200) 4096 3719)/2)
    have hp : cPayment 3718 = (12251183503:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3718+point (1327/200) 4096 3719)/2 = (7196099:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3718
  · change cPayment 3719 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3719+point (1327/200) 4096 3720)/2)
    have hp : cPayment 3719 = (12218113813:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3719+point (1327/200) 4096 3720)/2 = (7197153:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3719
  · change cPayment 3720 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3720+point (1327/200) 4096 3721)/2)
    have hp : cPayment 3720 = (12185047108:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3720+point (1327/200) 4096 3721)/2 = (7198207:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3720
  · change cPayment 3721 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3721+point (1327/200) 4096 3722)/2)
    have hp : cPayment 3721 = (12151983391:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3721+point (1327/200) 4096 3722)/2 = (7199261:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3721
  · change cPayment 3722 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3722+point (1327/200) 4096 3723)/2)
    have hp : cPayment 3722 = (12118922665:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3722+point (1327/200) 4096 3723)/2 = (1440063:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3722
  · change cPayment 3723 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3723+point (1327/200) 4096 3724)/2)
    have hp : cPayment 3723 = (12085864932:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3723+point (1327/200) 4096 3724)/2 = (7201369:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3723
  · change cPayment 3724 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3724+point (1327/200) 4096 3725)/2)
    have hp : cPayment 3724 = (12052810195:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3724+point (1327/200) 4096 3725)/2 = (7202423:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3724
  · change cPayment 3725 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3725+point (1327/200) 4096 3726)/2)
    have hp : cPayment 3725 = (12019758456:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3725+point (1327/200) 4096 3726)/2 = (7203477:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3725
  · change cPayment 3726 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3726+point (1327/200) 4096 3727)/2)
    have hp : cPayment 3726 = (11986709718:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3726+point (1327/200) 4096 3727)/2 = (7204531:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3726
  · change cPayment 3727 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3727+point (1327/200) 4096 3728)/2)
    have hp : cPayment 3727 = (11953663984:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3727+point (1327/200) 4096 3728)/2 = (1441117:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3727
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_232
