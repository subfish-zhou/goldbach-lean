import WR2ClassicalCPayments
import WR2ClassicalCPoints176
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_176 (j : Fin 16) : cPayment (16*176+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*176+j.val)+point (1327/200) 4096 (16*176+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2816 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2816+point (1327/200) 4096 2817)/2)
    have hp : cPayment 2816 = (42827738607:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2816+point (1327/200) 4096 2817)/2 = (6245391:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2816
  · change cPayment 2817 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2817+point (1327/200) 4096 2818)/2)
    have hp : cPayment 2817 = (42793727460:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2817+point (1327/200) 4096 2818)/2 = (1249289:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2817
  · change cPayment 2818 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2818+point (1327/200) 4096 2819)/2)
    have hp : cPayment 2818 = (42759714434:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2818+point (1327/200) 4096 2819)/2 = (6247499:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2818
  · change cPayment 2819 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2819+point (1327/200) 4096 2820)/2)
    have hp : cPayment 2819 = (42725699538:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2819+point (1327/200) 4096 2820)/2 = (6248553:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2819
  · change cPayment 2820 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2820+point (1327/200) 4096 2821)/2)
    have hp : cPayment 2820 = (42691682780:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2820+point (1327/200) 4096 2821)/2 = (6249607:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2820
  · change cPayment 2821 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2821+point (1327/200) 4096 2822)/2)
    have hp : cPayment 2821 = (42657664170:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2821+point (1327/200) 4096 2822)/2 = (6250661:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2821
  · change cPayment 2822 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2822+point (1327/200) 4096 2823)/2)
    have hp : cPayment 2822 = (42623643719:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2822+point (1327/200) 4096 2823)/2 = (1250343:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2822
  · change cPayment 2823 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2823+point (1327/200) 4096 2824)/2)
    have hp : cPayment 2823 = (42589621434:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2823+point (1327/200) 4096 2824)/2 = (6252769:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2823
  · change cPayment 2824 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2824+point (1327/200) 4096 2825)/2)
    have hp : cPayment 2824 = (42555597325:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2824+point (1327/200) 4096 2825)/2 = (6253823:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2824
  · change cPayment 2825 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2825+point (1327/200) 4096 2826)/2)
    have hp : cPayment 2825 = (42521571402:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2825+point (1327/200) 4096 2826)/2 = (6254877:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2825
  · change cPayment 2826 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2826+point (1327/200) 4096 2827)/2)
    have hp : cPayment 2826 = (42487543674:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2826+point (1327/200) 4096 2827)/2 = (6255931:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2826
  · change cPayment 2827 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2827+point (1327/200) 4096 2828)/2)
    have hp : cPayment 2827 = (42453514150:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2827+point (1327/200) 4096 2828)/2 = (1251397:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2827
  · change cPayment 2828 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2828+point (1327/200) 4096 2829)/2)
    have hp : cPayment 2828 = (42419482838:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2828+point (1327/200) 4096 2829)/2 = (6258039:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2828
  · change cPayment 2829 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2829+point (1327/200) 4096 2830)/2)
    have hp : cPayment 2829 = (42385449750:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2829+point (1327/200) 4096 2830)/2 = (6259093:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2829
  · change cPayment 2830 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2830+point (1327/200) 4096 2831)/2)
    have hp : cPayment 2830 = (42351414893:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2830+point (1327/200) 4096 2831)/2 = (6260147:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2830
  · change cPayment 2831 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2831+point (1327/200) 4096 2832)/2)
    have hp : cPayment 2831 = (42317378277:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2831+point (1327/200) 4096 2832)/2 = (6261201:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2831
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_176
