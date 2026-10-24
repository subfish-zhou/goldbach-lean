import WR2ClassicalCPayments
import WR2ClassicalCPoints047
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_047 (j : Fin 16) : cPayment (16*47+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*47+j.val)+point (1327/200) 4096 (16*47+j.val+1))/2) := by
  fin_cases j
  · change cPayment 752 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 752+point (1327/200) 4096 753)/2)
    have hp : cPayment 752 = (76413098174:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 752+point (1327/200) 4096 753)/2 = (813987:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_752
  · change cPayment 753 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 753+point (1327/200) 4096 754)/2)
    have hp : cPayment 753 = (76447804280:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 753+point (1327/200) 4096 754)/2 = (4070989:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_753
  · change cPayment 754 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 754+point (1327/200) 4096 755)/2)
    have hp : cPayment 754 = (76482397171:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 754+point (1327/200) 4096 755)/2 = (4072043:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_754
  · change cPayment 755 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 755+point (1327/200) 4096 756)/2)
    have hp : cPayment 755 = (76516877022:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 755+point (1327/200) 4096 756)/2 = (4073097:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_755
  · change cPayment 756 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 756+point (1327/200) 4096 757)/2)
    have hp : cPayment 756 = (76551244011:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 756+point (1327/200) 4096 757)/2 = (4074151:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_756
  · change cPayment 757 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 757+point (1327/200) 4096 758)/2)
    have hp : cPayment 757 = (76585498313:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 757+point (1327/200) 4096 758)/2 = (815041:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_757
  · change cPayment 758 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 758+point (1327/200) 4096 759)/2)
    have hp : cPayment 758 = (76619640105:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 758+point (1327/200) 4096 759)/2 = (4076259:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_758
  · change cPayment 759 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 759+point (1327/200) 4096 760)/2)
    have hp : cPayment 759 = (76653669562:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 759+point (1327/200) 4096 760)/2 = (4077313:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_759
  · change cPayment 760 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 760+point (1327/200) 4096 761)/2)
    have hp : cPayment 760 = (76687586860:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 760+point (1327/200) 4096 761)/2 = (4078367:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_760
  · change cPayment 761 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 761+point (1327/200) 4096 762)/2)
    have hp : cPayment 761 = (76721392174:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 761+point (1327/200) 4096 762)/2 = (4079421:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_761
  · change cPayment 762 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 762+point (1327/200) 4096 763)/2)
    have hp : cPayment 762 = (76755085678:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 762+point (1327/200) 4096 763)/2 = (163219:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_762
  · change cPayment 763 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 763+point (1327/200) 4096 764)/2)
    have hp : cPayment 763 = (76788667549:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 763+point (1327/200) 4096 764)/2 = (4081529:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_763
  · change cPayment 764 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 764+point (1327/200) 4096 765)/2)
    have hp : cPayment 764 = (76822137959:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 764+point (1327/200) 4096 765)/2 = (4082583:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_764
  · change cPayment 765 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 765+point (1327/200) 4096 766)/2)
    have hp : cPayment 765 = (76855497082:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 765+point (1327/200) 4096 766)/2 = (4083637:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_765
  · change cPayment 766 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 766+point (1327/200) 4096 767)/2)
    have hp : cPayment 766 = (76888745094:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 766+point (1327/200) 4096 767)/2 = (4084691:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_766
  · change cPayment 767 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 767+point (1327/200) 4096 768)/2)
    have hp : cPayment 767 = (76921882166:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 767+point (1327/200) 4096 768)/2 = (817149:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_767
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_047
