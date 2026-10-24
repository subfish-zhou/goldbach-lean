import WR2ClassicalCPayments
import WR2ClassicalCPoints185
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_185 (j : Fin 16) : cPayment (16*185+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*185+j.val)+point (1327/200) 4096 (16*185+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2960 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2960+point (1327/200) 4096 2961)/2)
    have hp : cPayment 2960 = (37915134503:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2960+point (1327/200) 4096 2961)/2 = (6397167:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2960
  · change cPayment 2961 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2961+point (1327/200) 4096 2962)/2)
    have hp : cPayment 2961 = (37880943237:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2961+point (1327/200) 4096 2962)/2 = (6398221:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2961
  · change cPayment 2962 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2962+point (1327/200) 4096 2963)/2)
    have hp : cPayment 2962 = (37846751319:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2962+point (1327/200) 4096 2963)/2 = (255971:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2962
  · change cPayment 2963 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2963+point (1327/200) 4096 2964)/2)
    have hp : cPayment 2963 = (37812558756:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2963+point (1327/200) 4096 2964)/2 = (6400329:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2963
  · change cPayment 2964 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2964+point (1327/200) 4096 2965)/2)
    have hp : cPayment 2964 = (37778365555:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2964+point (1327/200) 4096 2965)/2 = (6401383:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2964
  · change cPayment 2965 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2965+point (1327/200) 4096 2966)/2)
    have hp : cPayment 2965 = (37744171725:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2965+point (1327/200) 4096 2966)/2 = (6402437:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2965
  · change cPayment 2966 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2966+point (1327/200) 4096 2967)/2)
    have hp : cPayment 2966 = (37709977273:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2966+point (1327/200) 4096 2967)/2 = (6403491:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2966
  · change cPayment 2967 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2967+point (1327/200) 4096 2968)/2)
    have hp : cPayment 2967 = (37675782207:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2967+point (1327/200) 4096 2968)/2 = (1280909:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2967
  · change cPayment 2968 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2968+point (1327/200) 4096 2969)/2)
    have hp : cPayment 2968 = (37641586534:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2968+point (1327/200) 4096 2969)/2 = (6405599:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2968
  · change cPayment 2969 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2969+point (1327/200) 4096 2970)/2)
    have hp : cPayment 2969 = (37607390263:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2969+point (1327/200) 4096 2970)/2 = (6406653:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2969
  · change cPayment 2970 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2970+point (1327/200) 4096 2971)/2)
    have hp : cPayment 2970 = (37573193401:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2970+point (1327/200) 4096 2971)/2 = (6407707:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2970
  · change cPayment 2971 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2971+point (1327/200) 4096 2972)/2)
    have hp : cPayment 2971 = (37538995955:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2971+point (1327/200) 4096 2972)/2 = (6408761:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2971
  · change cPayment 2972 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2972+point (1327/200) 4096 2973)/2)
    have hp : cPayment 2972 = (37504797933:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2972+point (1327/200) 4096 2973)/2 = (1281963:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2972
  · change cPayment 2973 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2973+point (1327/200) 4096 2974)/2)
    have hp : cPayment 2973 = (37470599342:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2973+point (1327/200) 4096 2974)/2 = (6410869:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2973
  · change cPayment 2974 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2974+point (1327/200) 4096 2975)/2)
    have hp : cPayment 2974 = (37436400192:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2974+point (1327/200) 4096 2975)/2 = (6411923:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2974
  · change cPayment 2975 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2975+point (1327/200) 4096 2976)/2)
    have hp : cPayment 2975 = (37402200488:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2975+point (1327/200) 4096 2976)/2 = (6412977:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2975
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_185
