import WR2ClassicalCPayments
import WR2ClassicalCPoints041
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_041 (j : Fin 16) : cPayment (16*41+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*41+j.val)+point (1327/200) 4096 (16*41+j.val+1))/2) := by
  fin_cases j
  · change cPayment 656 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 656+point (1327/200) 4096 657)/2)
    have hp : cPayment 656 = (72526111262:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 656+point (1327/200) 4096 657)/2 = (3968751:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_656
  · change cPayment 657 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 657+point (1327/200) 4096 658)/2)
    have hp : cPayment 657 = (72572557040:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 657+point (1327/200) 4096 658)/2 = (793961:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_657
  · change cPayment 658 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 658+point (1327/200) 4096 659)/2)
    have hp : cPayment 658 = (72618871151:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 658+point (1327/200) 4096 659)/2 = (3970859:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_658
  · change cPayment 659 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 659+point (1327/200) 4096 660)/2)
    have hp : cPayment 659 = (72665053804:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 659+point (1327/200) 4096 660)/2 = (3971913:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_659
  · change cPayment 660 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 660+point (1327/200) 4096 661)/2)
    have hp : cPayment 660 = (72711105205:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 660+point (1327/200) 4096 661)/2 = (3972967:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_660
  · change cPayment 661 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 661+point (1327/200) 4096 662)/2)
    have hp : cPayment 661 = (72757025562:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 661+point (1327/200) 4096 662)/2 = (3974021:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_661
  · change cPayment 662 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 662+point (1327/200) 4096 663)/2)
    have hp : cPayment 662 = (72802815083:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 662+point (1327/200) 4096 663)/2 = (159003:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_662
  · change cPayment 663 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 663+point (1327/200) 4096 664)/2)
    have hp : cPayment 663 = (72848473973:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 663+point (1327/200) 4096 664)/2 = (3976129:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_663
  · change cPayment 664 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 664+point (1327/200) 4096 665)/2)
    have hp : cPayment 664 = (72894002440:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 664+point (1327/200) 4096 665)/2 = (3977183:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_664
  · change cPayment 665 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 665+point (1327/200) 4096 666)/2)
    have hp : cPayment 665 = (72939400689:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 665+point (1327/200) 4096 666)/2 = (3978237:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_665
  · change cPayment 666 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 666+point (1327/200) 4096 667)/2)
    have hp : cPayment 666 = (72984668926:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 666+point (1327/200) 4096 667)/2 = (3979291:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_666
  · change cPayment 667 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 667+point (1327/200) 4096 668)/2)
    have hp : cPayment 667 = (73029807356:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 667+point (1327/200) 4096 668)/2 = (796069:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_667
  · change cPayment 668 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 668+point (1327/200) 4096 669)/2)
    have hp : cPayment 668 = (73074816185:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 668+point (1327/200) 4096 669)/2 = (3981399:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_668
  · change cPayment 669 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 669+point (1327/200) 4096 670)/2)
    have hp : cPayment 669 = (73119695616:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 669+point (1327/200) 4096 670)/2 = (3982453:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_669
  · change cPayment 670 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 670+point (1327/200) 4096 671)/2)
    have hp : cPayment 670 = (73164445854:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 670+point (1327/200) 4096 671)/2 = (3983507:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_670
  · change cPayment 671 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 671+point (1327/200) 4096 672)/2)
    have hp : cPayment 671 = (73209067103:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 671+point (1327/200) 4096 672)/2 = (3984561:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_671
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_041
