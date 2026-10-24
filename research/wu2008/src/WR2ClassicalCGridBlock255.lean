import WR2ClassicalCPayments
import WR2ClassicalCPoints255
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_255 (j : Fin 16) : cPayment (16*255+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*255+j.val)+point (1327/200) 4096 (16*255+j.val+1))/2) := by
  fin_cases j
  · change cPayment 4080 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4080+point (1327/200) 4096 4081)/2)
    have hp : cPayment 4080 = (493171474:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4080+point (1327/200) 4096 4081)/2 = (7577647:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4080
  · change cPayment 4081 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4081+point (1327/200) 4096 4082)/2)
    have hp : cPayment 4081 = (461326984:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4081+point (1327/200) 4096 4082)/2 = (7578701:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4081
  · change cPayment 4082 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4082+point (1327/200) 4096 4083)/2)
    have hp : cPayment 4082 = (429486208:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4082+point (1327/200) 4096 4083)/2 = (1515951:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4082
  · change cPayment 4083 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4083+point (1327/200) 4096 4084)/2)
    have hp : cPayment 4083 = (397649148:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4083+point (1327/200) 4096 4084)/2 = (7580809:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4083
  · change cPayment 4084 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4084+point (1327/200) 4096 4085)/2)
    have hp : cPayment 4084 = (365815806:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4084+point (1327/200) 4096 4085)/2 = (7581863:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4084
  · change cPayment 4085 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4085+point (1327/200) 4096 4086)/2)
    have hp : cPayment 4085 = (333986181:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4085+point (1327/200) 4096 4086)/2 = (7582917:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4085
  · change cPayment 4086 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4086+point (1327/200) 4096 4087)/2)
    have hp : cPayment 4086 = (302160277:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4086+point (1327/200) 4096 4087)/2 = (7583971:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4086
  · change cPayment 4087 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4087+point (1327/200) 4096 4088)/2)
    have hp : cPayment 4087 = (270338094:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4087+point (1327/200) 4096 4088)/2 = (303401:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4087
  · change cPayment 4088 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4088+point (1327/200) 4096 4089)/2)
    have hp : cPayment 4088 = (238519635:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4088+point (1327/200) 4096 4089)/2 = (7586079:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4088
  · change cPayment 4089 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4089+point (1327/200) 4096 4090)/2)
    have hp : cPayment 4089 = (206704899:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4089+point (1327/200) 4096 4090)/2 = (7587133:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4089
  · change cPayment 4090 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4090+point (1327/200) 4096 4091)/2)
    have hp : cPayment 4090 = (174893890:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4090+point (1327/200) 4096 4091)/2 = (7588187:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4090
  · change cPayment 4091 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4091+point (1327/200) 4096 4092)/2)
    have hp : cPayment 4091 = (143086607:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4091+point (1327/200) 4096 4092)/2 = (7589241:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4091
  · change cPayment 4092 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4092+point (1327/200) 4096 4093)/2)
    have hp : cPayment 4092 = (111283053:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4092+point (1327/200) 4096 4093)/2 = (1518059:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4092
  · change cPayment 4093 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4093+point (1327/200) 4096 4094)/2)
    have hp : cPayment 4093 = (79483230:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4093+point (1327/200) 4096 4094)/2 = (7591349:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4093
  · change cPayment 4094 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4094+point (1327/200) 4096 4095)/2)
    have hp : cPayment 4094 = (47687138:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4094+point (1327/200) 4096 4095)/2 = (7592403:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4094
  · change cPayment 4095 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4095+point (1327/200) 4096 4096)/2)
    have hp : cPayment 4095 = (15894779:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4095+point (1327/200) 4096 4096)/2 = (7593457:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4095
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_255
