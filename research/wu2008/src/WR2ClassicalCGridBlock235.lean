import WR2ClassicalCPayments
import WR2ClassicalCPoints235
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_235 (j : Fin 16) : cPayment (16*235+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*235+j.val)+point (1327/200) 4096 (16*235+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3760 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3760+point (1327/200) 4096 3761)/2)
    have hp : cPayment 3760 = (10864856793:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3760+point (1327/200) 4096 3761)/2 = (7240367:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3760
  · change cPayment 3761 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3761+point (1327/200) 4096 3762)/2)
    have hp : cPayment 3761 = (10831914719:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3761+point (1327/200) 4096 3762)/2 = (7241421:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3761
  · change cPayment 3762 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3762+point (1327/200) 4096 3763)/2)
    have hp : cPayment 3762 = (10798975738:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3762+point (1327/200) 4096 3763)/2 = (289699:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3762
  · change cPayment 3763 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3763+point (1327/200) 4096 3764)/2)
    have hp : cPayment 3763 = (10766039853:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3763+point (1327/200) 4096 3764)/2 = (7243529:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3763
  · change cPayment 3764 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3764+point (1327/200) 4096 3765)/2)
    have hp : cPayment 3764 = (10733107066:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3764+point (1327/200) 4096 3765)/2 = (7244583:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3764
  · change cPayment 3765 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3765+point (1327/200) 4096 3766)/2)
    have hp : cPayment 3765 = (10700177379:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3765+point (1327/200) 4096 3766)/2 = (7245637:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3765
  · change cPayment 3766 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3766+point (1327/200) 4096 3767)/2)
    have hp : cPayment 3766 = (10667250796:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3766+point (1327/200) 4096 3767)/2 = (7246691:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3766
  · change cPayment 3767 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3767+point (1327/200) 4096 3768)/2)
    have hp : cPayment 3767 = (10634327318:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3767+point (1327/200) 4096 3768)/2 = (1449549:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3767
  · change cPayment 3768 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3768+point (1327/200) 4096 3769)/2)
    have hp : cPayment 3768 = (10601406948:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3768+point (1327/200) 4096 3769)/2 = (7248799:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3768
  · change cPayment 3769 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3769+point (1327/200) 4096 3770)/2)
    have hp : cPayment 3769 = (10568489688:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3769+point (1327/200) 4096 3770)/2 = (7249853:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3769
  · change cPayment 3770 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3770+point (1327/200) 4096 3771)/2)
    have hp : cPayment 3770 = (10535575541:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3770+point (1327/200) 4096 3771)/2 = (7250907:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3770
  · change cPayment 3771 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3771+point (1327/200) 4096 3772)/2)
    have hp : cPayment 3771 = (10502664510:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3771+point (1327/200) 4096 3772)/2 = (7251961:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3771
  · change cPayment 3772 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3772+point (1327/200) 4096 3773)/2)
    have hp : cPayment 3772 = (10469756596:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3772+point (1327/200) 4096 3773)/2 = (1450603:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3772
  · change cPayment 3773 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3773+point (1327/200) 4096 3774)/2)
    have hp : cPayment 3773 = (10436851803:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3773+point (1327/200) 4096 3774)/2 = (7254069:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3773
  · change cPayment 3774 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3774+point (1327/200) 4096 3775)/2)
    have hp : cPayment 3774 = (10403950132:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3774+point (1327/200) 4096 3775)/2 = (7255123:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3774
  · change cPayment 3775 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3775+point (1327/200) 4096 3776)/2)
    have hp : cPayment 3775 = (10371051587:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3775+point (1327/200) 4096 3776)/2 = (7256177:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3775
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_235
