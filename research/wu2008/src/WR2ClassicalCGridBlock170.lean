import WR2ClassicalCPayments
import WR2ClassicalCPoints170
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_170 (j : Fin 16) : cPayment (16*170+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*170+j.val)+point (1327/200) 4096 (16*170+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2720 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2720+point (1327/200) 4096 2721)/2)
    have hp : cPayment 2720 = (46082584988:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2720+point (1327/200) 4096 2721)/2 = (6144207:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2720
  · change cPayment 2721 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2721+point (1327/200) 4096 2722)/2)
    have hp : cPayment 2721 = (46048799828:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2721+point (1327/200) 4096 2722)/2 = (6145261:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2721
  · change cPayment 2722 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2722+point (1327/200) 4096 2723)/2)
    have hp : cPayment 2722 = (46015011829:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2722+point (1327/200) 4096 2723)/2 = (1229263:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2722
  · change cPayment 2723 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2723+point (1327/200) 4096 2724)/2)
    have hp : cPayment 2723 = (45981221003:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2723+point (1327/200) 4096 2724)/2 = (6147369:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2723
  · change cPayment 2724 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2724+point (1327/200) 4096 2725)/2)
    have hp : cPayment 2724 = (45947427359:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2724+point (1327/200) 4096 2725)/2 = (6148423:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2724
  · change cPayment 2725 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2725+point (1327/200) 4096 2726)/2)
    have hp : cPayment 2725 = (45913630908:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2725+point (1327/200) 4096 2726)/2 = (6149477:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2725
  · change cPayment 2726 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2726+point (1327/200) 4096 2727)/2)
    have hp : cPayment 2726 = (45879831661:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2726+point (1327/200) 4096 2727)/2 = (6150531:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2726
  · change cPayment 2727 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2727+point (1327/200) 4096 2728)/2)
    have hp : cPayment 2727 = (45846029628:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2727+point (1327/200) 4096 2728)/2 = (1230317:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2727
  · change cPayment 2728 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2728+point (1327/200) 4096 2729)/2)
    have hp : cPayment 2728 = (45812224820:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2728+point (1327/200) 4096 2729)/2 = (6152639:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2728
  · change cPayment 2729 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2729+point (1327/200) 4096 2730)/2)
    have hp : cPayment 2729 = (45778417248:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2729+point (1327/200) 4096 2730)/2 = (6153693:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2729
  · change cPayment 2730 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2730+point (1327/200) 4096 2731)/2)
    have hp : cPayment 2730 = (45744606921:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2730+point (1327/200) 4096 2731)/2 = (6154747:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2730
  · change cPayment 2731 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2731+point (1327/200) 4096 2732)/2)
    have hp : cPayment 2731 = (45710793851:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2731+point (1327/200) 4096 2732)/2 = (6155801:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2731
  · change cPayment 2732 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2732+point (1327/200) 4096 2733)/2)
    have hp : cPayment 2732 = (45676978048:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2732+point (1327/200) 4096 2733)/2 = (1231371:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2732
  · change cPayment 2733 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2733+point (1327/200) 4096 2734)/2)
    have hp : cPayment 2733 = (45643159523:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2733+point (1327/200) 4096 2734)/2 = (6157909:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2733
  · change cPayment 2734 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2734+point (1327/200) 4096 2735)/2)
    have hp : cPayment 2734 = (45609338285:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2734+point (1327/200) 4096 2735)/2 = (6158963:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2734
  · change cPayment 2735 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2735+point (1327/200) 4096 2736)/2)
    have hp : cPayment 2735 = (45575514346:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2735+point (1327/200) 4096 2736)/2 = (6160017:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2735
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_170
