import WR2ClassicalCPayments
import WR2ClassicalCPoints182
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_182 (j : Fin 16) : cPayment (16*182+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*182+j.val)+point (1327/200) 4096 (16*182+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2912 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2912+point (1327/200) 4096 2913)/2)
    have hp : cPayment 2912 = (39555393751:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2912+point (1327/200) 4096 2913)/2 = (253863:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2912
  · change cPayment 2913 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2913+point (1327/200) 4096 2914)/2)
    have hp : cPayment 2913 = (39521243101:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2913+point (1327/200) 4096 2914)/2 = (6347629:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2913
  · change cPayment 2914 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2914+point (1327/200) 4096 2915)/2)
    have hp : cPayment 2914 = (39487091415:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2914+point (1327/200) 4096 2915)/2 = (6348683:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2914
  · change cPayment 2915 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2915+point (1327/200) 4096 2916)/2)
    have hp : cPayment 2915 = (39452938701:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2915+point (1327/200) 4096 2916)/2 = (6349737:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2915
  · change cPayment 2916 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2916+point (1327/200) 4096 2917)/2)
    have hp : cPayment 2916 = (39418784969:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2916+point (1327/200) 4096 2917)/2 = (6350791:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2916
  · change cPayment 2917 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2917+point (1327/200) 4096 2918)/2)
    have hp : cPayment 2917 = (39384630225:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2917+point (1327/200) 4096 2918)/2 = (1270369:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2917
  · change cPayment 2918 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2918+point (1327/200) 4096 2919)/2)
    have hp : cPayment 2918 = (39350474478:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2918+point (1327/200) 4096 2919)/2 = (6352899:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2918
  · change cPayment 2919 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2919+point (1327/200) 4096 2920)/2)
    have hp : cPayment 2919 = (39316317736:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2919+point (1327/200) 4096 2920)/2 = (6353953:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2919
  · change cPayment 2920 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2920+point (1327/200) 4096 2921)/2)
    have hp : cPayment 2920 = (39282160008:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2920+point (1327/200) 4096 2921)/2 = (6355007:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2920
  · change cPayment 2921 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2921+point (1327/200) 4096 2922)/2)
    have hp : cPayment 2921 = (39248001302:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2921+point (1327/200) 4096 2922)/2 = (6356061:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2921
  · change cPayment 2922 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2922+point (1327/200) 4096 2923)/2)
    have hp : cPayment 2922 = (39213841625:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2922+point (1327/200) 4096 2923)/2 = (1271423:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2922
  · change cPayment 2923 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2923+point (1327/200) 4096 2924)/2)
    have hp : cPayment 2923 = (39179680986:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2923+point (1327/200) 4096 2924)/2 = (6358169:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2923
  · change cPayment 2924 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2924+point (1327/200) 4096 2925)/2)
    have hp : cPayment 2924 = (39145519393:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2924+point (1327/200) 4096 2925)/2 = (6359223:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2924
  · change cPayment 2925 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2925+point (1327/200) 4096 2926)/2)
    have hp : cPayment 2925 = (39111356855:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2925+point (1327/200) 4096 2926)/2 = (6360277:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2925
  · change cPayment 2926 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2926+point (1327/200) 4096 2927)/2)
    have hp : cPayment 2926 = (39077193379:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2926+point (1327/200) 4096 2927)/2 = (6361331:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2926
  · change cPayment 2927 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2927+point (1327/200) 4096 2928)/2)
    have hp : cPayment 2927 = (39043028973:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2927+point (1327/200) 4096 2928)/2 = (1272477:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2927
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_182
