import WR2ClassicalCPayments
import WR2ClassicalCPoints196
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_196 (j : Fin 16) : cPayment (16*196+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*196+j.val)+point (1327/200) 4096 (16*196+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3136 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3136+point (1327/200) 4096 3137)/2)
    have hp : cPayment 3136 = (31893936091:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3136+point (1327/200) 4096 3137)/2 = (6582671:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3136
  · change cPayment 3137 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3137+point (1327/200) 4096 3138)/2)
    have hp : cPayment 3137 = (31859740136:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3137+point (1327/200) 4096 3138)/2 = (263349:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3137
  · change cPayment 3138 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3138+point (1327/200) 4096 3139)/2)
    have hp : cPayment 3138 = (31825544739:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3138+point (1327/200) 4096 3139)/2 = (6584779:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3138
  · change cPayment 3139 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3139+point (1327/200) 4096 3140)/2)
    have hp : cPayment 3139 = (31791349906:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3139+point (1327/200) 4096 3140)/2 = (6585833:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3139
  · change cPayment 3140 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3140+point (1327/200) 4096 3141)/2)
    have hp : cPayment 3140 = (31757155644:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3140+point (1327/200) 4096 3141)/2 = (6586887:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3140
  · change cPayment 3141 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3141+point (1327/200) 4096 3142)/2)
    have hp : cPayment 3141 = (31722961959:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3141+point (1327/200) 4096 3142)/2 = (6587941:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3141
  · change cPayment 3142 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3142+point (1327/200) 4096 3143)/2)
    have hp : cPayment 3142 = (31688768856:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3142+point (1327/200) 4096 3143)/2 = (1317799:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3142
  · change cPayment 3143 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3143+point (1327/200) 4096 3144)/2)
    have hp : cPayment 3143 = (31654576342:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3143+point (1327/200) 4096 3144)/2 = (6590049:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3143
  · change cPayment 3144 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3144+point (1327/200) 4096 3145)/2)
    have hp : cPayment 3144 = (31620384423:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3144+point (1327/200) 4096 3145)/2 = (6591103:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3144
  · change cPayment 3145 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3145+point (1327/200) 4096 3146)/2)
    have hp : cPayment 3145 = (31586193104:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3145+point (1327/200) 4096 3146)/2 = (6592157:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3145
  · change cPayment 3146 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3146+point (1327/200) 4096 3147)/2)
    have hp : cPayment 3146 = (31552002393:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3146+point (1327/200) 4096 3147)/2 = (6593211:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3146
  · change cPayment 3147 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3147+point (1327/200) 4096 3148)/2)
    have hp : cPayment 3147 = (31517812294:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3147+point (1327/200) 4096 3148)/2 = (1318853:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3147
  · change cPayment 3148 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3148+point (1327/200) 4096 3149)/2)
    have hp : cPayment 3148 = (31483622814:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3148+point (1327/200) 4096 3149)/2 = (6595319:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3148
  · change cPayment 3149 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3149+point (1327/200) 4096 3150)/2)
    have hp : cPayment 3149 = (31449433959:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3149+point (1327/200) 4096 3150)/2 = (6596373:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3149
  · change cPayment 3150 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3150+point (1327/200) 4096 3151)/2)
    have hp : cPayment 3150 = (31415245735:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3150+point (1327/200) 4096 3151)/2 = (6597427:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3150
  · change cPayment 3151 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3151+point (1327/200) 4096 3152)/2)
    have hp : cPayment 3151 = (31381058148:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3151+point (1327/200) 4096 3152)/2 = (6598481:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3151
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_196
