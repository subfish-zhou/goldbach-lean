import WR2ClassicalCPayments
import WR2ClassicalCPoints168
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_168 (j : Fin 16) : cPayment (16*168+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*168+j.val)+point (1327/200) 4096 (16*168+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2688 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2688+point (1327/200) 4096 2689)/2)
    have hp : cPayment 2688 = (47162146920:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2688+point (1327/200) 4096 2689)/2 = (6110479:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2688
  · change cPayment 2689 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2689+point (1327/200) 4096 2690)/2)
    have hp : cPayment 2689 = (47128458296:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2689+point (1327/200) 4096 2690)/2 = (6111533:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2689
  · change cPayment 2690 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2690+point (1327/200) 4096 2691)/2)
    have hp : cPayment 2690 = (47094766486:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2690+point (1327/200) 4096 2691)/2 = (6112587:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2690
  · change cPayment 2691 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2691+point (1327/200) 4096 2692)/2)
    have hp : cPayment 2691 = (47061071501:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2691+point (1327/200) 4096 2692)/2 = (6113641:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2691
  · change cPayment 2692 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2692+point (1327/200) 4096 2693)/2)
    have hp : cPayment 2692 = (47027373351:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2692+point (1327/200) 4096 2693)/2 = (1222939:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2692
  · change cPayment 2693 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2693+point (1327/200) 4096 2694)/2)
    have hp : cPayment 2693 = (46993672049:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2693+point (1327/200) 4096 2694)/2 = (6115749:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2693
  · change cPayment 2694 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2694+point (1327/200) 4096 2695)/2)
    have hp : cPayment 2694 = (46959967604:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2694+point (1327/200) 4096 2695)/2 = (6116803:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2694
  · change cPayment 2695 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2695+point (1327/200) 4096 2696)/2)
    have hp : cPayment 2695 = (46926260028:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2695+point (1327/200) 4096 2696)/2 = (6117857:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2695
  · change cPayment 2696 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2696+point (1327/200) 4096 2697)/2)
    have hp : cPayment 2696 = (46892549332:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2696+point (1327/200) 4096 2697)/2 = (6118911:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2696
  · change cPayment 2697 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2697+point (1327/200) 4096 2698)/2)
    have hp : cPayment 2697 = (46858835526:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2697+point (1327/200) 4096 2698)/2 = (1223993:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2697
  · change cPayment 2698 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2698+point (1327/200) 4096 2699)/2)
    have hp : cPayment 2698 = (46825118623:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2698+point (1327/200) 4096 2699)/2 = (6121019:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2698
  · change cPayment 2699 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2699+point (1327/200) 4096 2700)/2)
    have hp : cPayment 2699 = (46791398632:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2699+point (1327/200) 4096 2700)/2 = (6122073:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2699
  · change cPayment 2700 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2700+point (1327/200) 4096 2701)/2)
    have hp : cPayment 2700 = (46757675566:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2700+point (1327/200) 4096 2701)/2 = (6123127:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2700
  · change cPayment 2701 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2701+point (1327/200) 4096 2702)/2)
    have hp : cPayment 2701 = (46723949434:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2701+point (1327/200) 4096 2702)/2 = (6124181:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2701
  · change cPayment 2702 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2702+point (1327/200) 4096 2703)/2)
    have hp : cPayment 2702 = (46690220248:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2702+point (1327/200) 4096 2703)/2 = (1225047:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2702
  · change cPayment 2703 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2703+point (1327/200) 4096 2704)/2)
    have hp : cPayment 2703 = (46656488018:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2703+point (1327/200) 4096 2704)/2 = (6126289:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2703
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_168
