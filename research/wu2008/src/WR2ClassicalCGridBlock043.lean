import WR2ClassicalCPayments
import WR2ClassicalCPoints043
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_043 (j : Fin 16) : cPayment (16*43+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*43+j.val)+point (1327/200) 4096 (16*43+j.val+1))/2) := by
  fin_cases j
  · change cPayment 688 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 688+point (1327/200) 4096 689)/2)
    have hp : cPayment 688 = (73948088887:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 688+point (1327/200) 4096 689)/2 = (4002479:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_688
  · change cPayment 689 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 689+point (1327/200) 4096 690)/2)
    have hp : cPayment 689 = (73990422803:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 689+point (1327/200) 4096 690)/2 = (4003533:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_689
  · change cPayment 690 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 690+point (1327/200) 4096 691)/2)
    have hp : cPayment 690 = (74032631538:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 690+point (1327/200) 4096 691)/2 = (4004587:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_690
  · change cPayment 691 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 691+point (1327/200) 4096 692)/2)
    have hp : cPayment 691 = (74074715290:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 691+point (1327/200) 4096 692)/2 = (4005641:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_691
  · change cPayment 692 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 692+point (1327/200) 4096 693)/2)
    have hp : cPayment 692 = (74116674254:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 692+point (1327/200) 4096 693)/2 = (801339:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_692
  · change cPayment 693 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 693+point (1327/200) 4096 694)/2)
    have hp : cPayment 693 = (74158508629:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 693+point (1327/200) 4096 694)/2 = (4007749:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_693
  · change cPayment 694 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 694+point (1327/200) 4096 695)/2)
    have hp : cPayment 694 = (74200218608:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 694+point (1327/200) 4096 695)/2 = (4008803:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_694
  · change cPayment 695 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 695+point (1327/200) 4096 696)/2)
    have hp : cPayment 695 = (74241804390:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 695+point (1327/200) 4096 696)/2 = (4009857:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_695
  · change cPayment 696 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 696+point (1327/200) 4096 697)/2)
    have hp : cPayment 696 = (74283266168:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 696+point (1327/200) 4096 697)/2 = (4010911:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_696
  · change cPayment 697 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 697+point (1327/200) 4096 698)/2)
    have hp : cPayment 697 = (74324604138:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 697+point (1327/200) 4096 698)/2 = (802393:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_697
  · change cPayment 698 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 698+point (1327/200) 4096 699)/2)
    have hp : cPayment 698 = (74365818494:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 698+point (1327/200) 4096 699)/2 = (4013019:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_698
  · change cPayment 699 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 699+point (1327/200) 4096 700)/2)
    have hp : cPayment 699 = (74406909431:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 699+point (1327/200) 4096 700)/2 = (4014073:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_699
  · change cPayment 700 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 700+point (1327/200) 4096 701)/2)
    have hp : cPayment 700 = (74447877144:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 700+point (1327/200) 4096 701)/2 = (4015127:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_700
  · change cPayment 701 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 701+point (1327/200) 4096 702)/2)
    have hp : cPayment 701 = (74488721825:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 701+point (1327/200) 4096 702)/2 = (4016181:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_701
  · change cPayment 702 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 702+point (1327/200) 4096 703)/2)
    have hp : cPayment 702 = (74529443668:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 702+point (1327/200) 4096 703)/2 = (803447:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_702
  · change cPayment 703 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 703+point (1327/200) 4096 704)/2)
    have hp : cPayment 703 = (74570042867:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 703+point (1327/200) 4096 704)/2 = (4018289:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_703
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_043
