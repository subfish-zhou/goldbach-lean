import WR2ClassicalCPayments
import WR2ClassicalCPoints180
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_180 (j : Fin 16) : cPayment (16*180+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*180+j.val)+point (1327/200) 4096 (16*180+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2880 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2880+point (1327/200) 4096 2881)/2)
    have hp : cPayment 2880 = (40647617810:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2880+point (1327/200) 4096 2881)/2 = (6312847:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2880
  · change cPayment 2881 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2881+point (1327/200) 4096 2882)/2)
    have hp : cPayment 2881 = (40613504719:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2881+point (1327/200) 4096 2882)/2 = (6313901:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2881
  · change cPayment 2882 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2882+point (1327/200) 4096 2883)/2)
    have hp : cPayment 2882 = (40579390323:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2882+point (1327/200) 4096 2883)/2 = (1262991:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2882
  · change cPayment 2883 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2883+point (1327/200) 4096 2884)/2)
    have hp : cPayment 2883 = (40545274631:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2883+point (1327/200) 4096 2884)/2 = (6316009:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2883
  · change cPayment 2884 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2884+point (1327/200) 4096 2885)/2)
    have hp : cPayment 2884 = (40511157650:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2884+point (1327/200) 4096 2885)/2 = (6317063:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2884
  · change cPayment 2885 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2885+point (1327/200) 4096 2886)/2)
    have hp : cPayment 2885 = (40477039390:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2885+point (1327/200) 4096 2886)/2 = (6318117:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2885
  · change cPayment 2886 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2886+point (1327/200) 4096 2887)/2)
    have hp : cPayment 2886 = (40442919859:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2886+point (1327/200) 4096 2887)/2 = (6319171:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2886
  · change cPayment 2887 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2887+point (1327/200) 4096 2888)/2)
    have hp : cPayment 2887 = (40408799066:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2887+point (1327/200) 4096 2888)/2 = (252809:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2887
  · change cPayment 2888 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2888+point (1327/200) 4096 2889)/2)
    have hp : cPayment 2888 = (40374677019:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2888+point (1327/200) 4096 2889)/2 = (6321279:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2888
  · change cPayment 2889 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2889+point (1327/200) 4096 2890)/2)
    have hp : cPayment 2889 = (40340553727:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2889+point (1327/200) 4096 2890)/2 = (6322333:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2889
  · change cPayment 2890 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2890+point (1327/200) 4096 2891)/2)
    have hp : cPayment 2890 = (40306429198:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2890+point (1327/200) 4096 2891)/2 = (6323387:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2890
  · change cPayment 2891 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2891+point (1327/200) 4096 2892)/2)
    have hp : cPayment 2891 = (40272303440:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2891+point (1327/200) 4096 2892)/2 = (6324441:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2891
  · change cPayment 2892 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2892+point (1327/200) 4096 2893)/2)
    have hp : cPayment 2892 = (40238176463:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2892+point (1327/200) 4096 2893)/2 = (1265099:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2892
  · change cPayment 2893 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2893+point (1327/200) 4096 2894)/2)
    have hp : cPayment 2893 = (40204048275:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2893+point (1327/200) 4096 2894)/2 = (6326549:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2893
  · change cPayment 2894 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2894+point (1327/200) 4096 2895)/2)
    have hp : cPayment 2894 = (40169918884:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2894+point (1327/200) 4096 2895)/2 = (6327603:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2894
  · change cPayment 2895 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2895+point (1327/200) 4096 2896)/2)
    have hp : cPayment 2895 = (40135788299:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2895+point (1327/200) 4096 2896)/2 = (6328657:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2895
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_180
