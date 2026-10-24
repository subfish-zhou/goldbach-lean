import WR2ClassicalCPayments
import WR2ClassicalCPoints193
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_193 (j : Fin 16) : cPayment (16*193+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*193+j.val)+point (1327/200) 4096 (16*193+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3088 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3088+point (1327/200) 4096 3089)/2)
    have hp : cPayment 3088 = (33535877122:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3088+point (1327/200) 4096 3089)/2 = (6532079:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3088
  · change cPayment 3089 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3089+point (1327/200) 4096 3090)/2)
    have hp : cPayment 3089 = (33501661692:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3089+point (1327/200) 4096 3090)/2 = (6533133:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3089
  · change cPayment 3090 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3090+point (1327/200) 4096 3091)/2)
    have hp : cPayment 3090 = (33467446518:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3090+point (1327/200) 4096 3091)/2 = (6534187:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3090
  · change cPayment 3091 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3091+point (1327/200) 4096 3092)/2)
    have hp : cPayment 3091 = (33433231607:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3091+point (1327/200) 4096 3092)/2 = (6535241:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3091
  · change cPayment 3092 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3092+point (1327/200) 4096 3093)/2)
    have hp : cPayment 3092 = (33399016965:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3092+point (1327/200) 4096 3093)/2 = (1307259:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3092
  · change cPayment 3093 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3093+point (1327/200) 4096 3094)/2)
    have hp : cPayment 3093 = (33364802598:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3093+point (1327/200) 4096 3094)/2 = (6537349:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3093
  · change cPayment 3094 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3094+point (1327/200) 4096 3095)/2)
    have hp : cPayment 3094 = (33330588513:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3094+point (1327/200) 4096 3095)/2 = (6538403:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3094
  · change cPayment 3095 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3095+point (1327/200) 4096 3096)/2)
    have hp : cPayment 3095 = (33296374717:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3095+point (1327/200) 4096 3096)/2 = (6539457:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3095
  · change cPayment 3096 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3096+point (1327/200) 4096 3097)/2)
    have hp : cPayment 3096 = (33262161216:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3096+point (1327/200) 4096 3097)/2 = (6540511:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3096
  · change cPayment 3097 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3097+point (1327/200) 4096 3098)/2)
    have hp : cPayment 3097 = (33227948017:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3097+point (1327/200) 4096 3098)/2 = (1308313:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3097
  · change cPayment 3098 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3098+point (1327/200) 4096 3099)/2)
    have hp : cPayment 3098 = (33193735125:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3098+point (1327/200) 4096 3099)/2 = (6542619:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3098
  · change cPayment 3099 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3099+point (1327/200) 4096 3100)/2)
    have hp : cPayment 3099 = (33159522547:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3099+point (1327/200) 4096 3100)/2 = (6543673:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3099
  · change cPayment 3100 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3100+point (1327/200) 4096 3101)/2)
    have hp : cPayment 3100 = (33125310290:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3100+point (1327/200) 4096 3101)/2 = (6544727:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3100
  · change cPayment 3101 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3101+point (1327/200) 4096 3102)/2)
    have hp : cPayment 3101 = (33091098361:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3101+point (1327/200) 4096 3102)/2 = (6545781:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3101
  · change cPayment 3102 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3102+point (1327/200) 4096 3103)/2)
    have hp : cPayment 3102 = (33056886764:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3102+point (1327/200) 4096 3103)/2 = (1309367:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3102
  · change cPayment 3103 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3103+point (1327/200) 4096 3104)/2)
    have hp : cPayment 3103 = (33022675508:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3103+point (1327/200) 4096 3104)/2 = (6547889:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3103
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_193
