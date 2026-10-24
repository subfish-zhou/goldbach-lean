import WR2ClassicalCPayments
import WR2ClassicalCPoints230
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_230 (j : Fin 16) : cPayment (16*230+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*230+j.val)+point (1327/200) 4096 (16*230+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3680 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3680+point (1327/200) 4096 3681)/2)
    have hp : cPayment 3680 = (13510017188:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3680+point (1327/200) 4096 3681)/2 = (7156047:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3680
  · change cPayment 3681 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3681+point (1327/200) 4096 3682)/2)
    have hp : cPayment 3681 = (13476836063:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3681+point (1327/200) 4096 3682)/2 = (7157101:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3681
  · change cPayment 3682 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3682+point (1327/200) 4096 3683)/2)
    have hp : cPayment 3682 = (13443657820:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3682+point (1327/200) 4096 3683)/2 = (1431631:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3682
  · change cPayment 3683 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3683+point (1327/200) 4096 3684)/2)
    have hp : cPayment 3683 = (13410482461:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3683+point (1327/200) 4096 3684)/2 = (7159209:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3683
  · change cPayment 3684 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3684+point (1327/200) 4096 3685)/2)
    have hp : cPayment 3684 = (13377309989:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3684+point (1327/200) 4096 3685)/2 = (7160263:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3684
  · change cPayment 3685 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3685+point (1327/200) 4096 3686)/2)
    have hp : cPayment 3685 = (13344140407:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3685+point (1327/200) 4096 3686)/2 = (7161317:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3685
  · change cPayment 3686 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3686+point (1327/200) 4096 3687)/2)
    have hp : cPayment 3686 = (13310973717:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3686+point (1327/200) 4096 3687)/2 = (7162371:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3686
  · change cPayment 3687 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3687+point (1327/200) 4096 3688)/2)
    have hp : cPayment 3687 = (13277809923:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3687+point (1327/200) 4096 3688)/2 = (286537:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3687
  · change cPayment 3688 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3688+point (1327/200) 4096 3689)/2)
    have hp : cPayment 3688 = (13244649028:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3688+point (1327/200) 4096 3689)/2 = (7164479:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3688
  · change cPayment 3689 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3689+point (1327/200) 4096 3690)/2)
    have hp : cPayment 3689 = (13211491033:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3689+point (1327/200) 4096 3690)/2 = (7165533:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3689
  · change cPayment 3690 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3690+point (1327/200) 4096 3691)/2)
    have hp : cPayment 3690 = (13178335943:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3690+point (1327/200) 4096 3691)/2 = (7166587:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3690
  · change cPayment 3691 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3691+point (1327/200) 4096 3692)/2)
    have hp : cPayment 3691 = (13145183758:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3691+point (1327/200) 4096 3692)/2 = (7167641:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3691
  · change cPayment 3692 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3692+point (1327/200) 4096 3693)/2)
    have hp : cPayment 3692 = (13112034484:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3692+point (1327/200) 4096 3693)/2 = (1433739:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3692
  · change cPayment 3693 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3693+point (1327/200) 4096 3694)/2)
    have hp : cPayment 3693 = (13078888121:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3693+point (1327/200) 4096 3694)/2 = (7169749:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3693
  · change cPayment 3694 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3694+point (1327/200) 4096 3695)/2)
    have hp : cPayment 3694 = (13045744673:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3694+point (1327/200) 4096 3695)/2 = (7170803:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3694
  · change cPayment 3695 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3695+point (1327/200) 4096 3696)/2)
    have hp : cPayment 3695 = (13012604143:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3695+point (1327/200) 4096 3696)/2 = (7171857:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3695
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_230
