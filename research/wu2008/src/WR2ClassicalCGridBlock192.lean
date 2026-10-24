import WR2ClassicalCPayments
import WR2ClassicalCPoints192
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_192 (j : Fin 16) : cPayment (16*192+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*192+j.val)+point (1327/200) 4096 (16*192+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3072 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3072+point (1327/200) 4096 3073)/2)
    have hp : cPayment 3072 = (34083353493:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3072+point (1327/200) 4096 3073)/2 = (1303043:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3072
  · change cPayment 3073 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3073+point (1327/200) 4096 3074)/2)
    have hp : cPayment 3073 = (34049134857:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3073+point (1327/200) 4096 3074)/2 = (6516269:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3073
  · change cPayment 3074 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3074+point (1327/200) 4096 3075)/2)
    have hp : cPayment 3074 = (34014916371:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3074+point (1327/200) 4096 3075)/2 = (6517323:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3074
  · change cPayment 3075 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3075+point (1327/200) 4096 3076)/2)
    have hp : cPayment 3075 = (33980698043:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3075+point (1327/200) 4096 3076)/2 = (6518377:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3075
  · change cPayment 3076 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3076+point (1327/200) 4096 3077)/2)
    have hp : cPayment 3076 = (33946479880:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3076+point (1327/200) 4096 3077)/2 = (6519431:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3076
  · change cPayment 3077 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3077+point (1327/200) 4096 3078)/2)
    have hp : cPayment 3077 = (33912261887:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3077+point (1327/200) 4096 3078)/2 = (1304097:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3077
  · change cPayment 3078 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3078+point (1327/200) 4096 3079)/2)
    have hp : cPayment 3078 = (33878044071:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3078+point (1327/200) 4096 3079)/2 = (6521539:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3078
  · change cPayment 3079 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3079+point (1327/200) 4096 3080)/2)
    have hp : cPayment 3079 = (33843826440:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3079+point (1327/200) 4096 3080)/2 = (6522593:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3079
  · change cPayment 3080 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3080+point (1327/200) 4096 3081)/2)
    have hp : cPayment 3080 = (33809608999:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3080+point (1327/200) 4096 3081)/2 = (6523647:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3080
  · change cPayment 3081 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3081+point (1327/200) 4096 3082)/2)
    have hp : cPayment 3081 = (33775391755:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3081+point (1327/200) 4096 3082)/2 = (6524701:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3081
  · change cPayment 3082 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3082+point (1327/200) 4096 3083)/2)
    have hp : cPayment 3082 = (33741174715:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3082+point (1327/200) 4096 3083)/2 = (1305151:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3082
  · change cPayment 3083 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3083+point (1327/200) 4096 3084)/2)
    have hp : cPayment 3083 = (33706957885:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3083+point (1327/200) 4096 3084)/2 = (6526809:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3083
  · change cPayment 3084 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3084+point (1327/200) 4096 3085)/2)
    have hp : cPayment 3084 = (33672741273:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3084+point (1327/200) 4096 3085)/2 = (6527863:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3084
  · change cPayment 3085 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3085+point (1327/200) 4096 3086)/2)
    have hp : cPayment 3085 = (33638524883:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3085+point (1327/200) 4096 3086)/2 = (6528917:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3085
  · change cPayment 3086 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3086+point (1327/200) 4096 3087)/2)
    have hp : cPayment 3086 = (33604308724:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3086+point (1327/200) 4096 3087)/2 = (6529971:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3086
  · change cPayment 3087 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3087+point (1327/200) 4096 3088)/2)
    have hp : cPayment 3087 = (33570092802:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3087+point (1327/200) 4096 3088)/2 = (261241:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3087
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_192
