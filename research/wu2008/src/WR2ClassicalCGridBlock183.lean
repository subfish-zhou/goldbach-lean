import WR2ClassicalCPayments
import WR2ClassicalCPoints183
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_183 (j : Fin 16) : cPayment (16*183+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*183+j.val)+point (1327/200) 4096 (16*183+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2928 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2928+point (1327/200) 4096 2929)/2)
    have hp : cPayment 2928 = (39008863646:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2928+point (1327/200) 4096 2929)/2 = (6363439:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2928
  · change cPayment 2929 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2929+point (1327/200) 4096 2930)/2)
    have hp : cPayment 2929 = (38974697405:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2929+point (1327/200) 4096 2930)/2 = (6364493:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2929
  · change cPayment 2930 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2930+point (1327/200) 4096 2931)/2)
    have hp : cPayment 2930 = (38940530260:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2930+point (1327/200) 4096 2931)/2 = (6365547:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2930
  · change cPayment 2931 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2931+point (1327/200) 4096 2932)/2)
    have hp : cPayment 2931 = (38906362216:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2931+point (1327/200) 4096 2932)/2 = (6366601:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2931
  · change cPayment 2932 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2932+point (1327/200) 4096 2933)/2)
    have hp : cPayment 2932 = (38872193284:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2932+point (1327/200) 4096 2933)/2 = (1273531:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2932
  · change cPayment 2933 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2933+point (1327/200) 4096 2934)/2)
    have hp : cPayment 2933 = (38838023470:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2933+point (1327/200) 4096 2934)/2 = (6368709:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2933
  · change cPayment 2934 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2934+point (1327/200) 4096 2935)/2)
    have hp : cPayment 2934 = (38803852784:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2934+point (1327/200) 4096 2935)/2 = (6369763:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2934
  · change cPayment 2935 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2935+point (1327/200) 4096 2936)/2)
    have hp : cPayment 2935 = (38769681232:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2935+point (1327/200) 4096 2936)/2 = (6370817:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2935
  · change cPayment 2936 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2936+point (1327/200) 4096 2937)/2)
    have hp : cPayment 2936 = (38735508823:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2936+point (1327/200) 4096 2937)/2 = (6371871:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2936
  · change cPayment 2937 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2937+point (1327/200) 4096 2938)/2)
    have hp : cPayment 2937 = (38701335565:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2937+point (1327/200) 4096 2938)/2 = (254917:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2937
  · change cPayment 2938 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2938+point (1327/200) 4096 2939)/2)
    have hp : cPayment 2938 = (38667161466:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2938+point (1327/200) 4096 2939)/2 = (6373979:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2938
  · change cPayment 2939 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2939+point (1327/200) 4096 2940)/2)
    have hp : cPayment 2939 = (38632986533:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2939+point (1327/200) 4096 2940)/2 = (6375033:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2939
  · change cPayment 2940 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2940+point (1327/200) 4096 2941)/2)
    have hp : cPayment 2940 = (38598810776:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2940+point (1327/200) 4096 2941)/2 = (6376087:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2940
  · change cPayment 2941 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2941+point (1327/200) 4096 2942)/2)
    have hp : cPayment 2941 = (38564634201:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2941+point (1327/200) 4096 2942)/2 = (6377141:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2941
  · change cPayment 2942 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2942+point (1327/200) 4096 2943)/2)
    have hp : cPayment 2942 = (38530456817:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2942+point (1327/200) 4096 2943)/2 = (1275639:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2942
  · change cPayment 2943 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2943+point (1327/200) 4096 2944)/2)
    have hp : cPayment 2943 = (38496278631:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2943+point (1327/200) 4096 2944)/2 = (6379249:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2943
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_183
