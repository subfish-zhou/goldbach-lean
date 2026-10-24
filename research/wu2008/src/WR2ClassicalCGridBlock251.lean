import WR2ClassicalCPayments
import WR2ClassicalCPoints251
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_251 (j : Fin 16) : cPayment (16*251+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*251+j.val)+point (1327/200) 4096 (16*251+j.val+1))/2) := by
  fin_cases j
  · change cPayment 4016 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4016+point (1327/200) 4096 4017)/2)
    have hp : cPayment 4016 = (2538875507:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4016+point (1327/200) 4096 4017)/2 = (7510191:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4016
  · change cPayment 4017 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4017+point (1327/200) 4096 4018)/2)
    have hp : cPayment 4017 = (2506796467:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4017+point (1327/200) 4096 4018)/2 = (1502249:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4017
  · change cPayment 4018 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4018+point (1327/200) 4096 4019)/2)
    have hp : cPayment 4018 = (2474721043:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4018+point (1327/200) 4096 4019)/2 = (7512299:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4018
  · change cPayment 4019 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4019+point (1327/200) 4096 4020)/2)
    have hp : cPayment 4019 = (2442649235:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4019+point (1327/200) 4096 4020)/2 = (7513353:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4019
  · change cPayment 4020 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4020+point (1327/200) 4096 4021)/2)
    have hp : cPayment 4020 = (2410581046:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4020+point (1327/200) 4096 4021)/2 = (7514407:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4020
  · change cPayment 4021 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4021+point (1327/200) 4096 4022)/2)
    have hp : cPayment 4021 = (2378516477:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4021+point (1327/200) 4096 4022)/2 = (7515461:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4021
  · change cPayment 4022 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4022+point (1327/200) 4096 4023)/2)
    have hp : cPayment 4022 = (2346455530:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4022+point (1327/200) 4096 4023)/2 = (1503303:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4022
  · change cPayment 4023 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4023+point (1327/200) 4096 4024)/2)
    have hp : cPayment 4023 = (2314398206:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4023+point (1327/200) 4096 4024)/2 = (7517569:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4023
  · change cPayment 4024 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4024+point (1327/200) 4096 4025)/2)
    have hp : cPayment 4024 = (2282344507:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4024+point (1327/200) 4096 4025)/2 = (7518623:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4024
  · change cPayment 4025 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4025+point (1327/200) 4096 4026)/2)
    have hp : cPayment 4025 = (2250294434:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4025+point (1327/200) 4096 4026)/2 = (7519677:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4025
  · change cPayment 4026 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4026+point (1327/200) 4096 4027)/2)
    have hp : cPayment 4026 = (2218247990:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4026+point (1327/200) 4096 4027)/2 = (7520731:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4026
  · change cPayment 4027 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4027+point (1327/200) 4096 4028)/2)
    have hp : cPayment 4027 = (2186205175:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4027+point (1327/200) 4096 4028)/2 = (1504357:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4027
  · change cPayment 4028 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4028+point (1327/200) 4096 4029)/2)
    have hp : cPayment 4028 = (2154165992:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4028+point (1327/200) 4096 4029)/2 = (7522839:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4028
  · change cPayment 4029 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4029+point (1327/200) 4096 4030)/2)
    have hp : cPayment 4029 = (2122130441:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4029+point (1327/200) 4096 4030)/2 = (7523893:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4029
  · change cPayment 4030 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4030+point (1327/200) 4096 4031)/2)
    have hp : cPayment 4030 = (2090098526:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4030+point (1327/200) 4096 4031)/2 = (7524947:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4030
  · change cPayment 4031 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4031+point (1327/200) 4096 4032)/2)
    have hp : cPayment 4031 = (2058070246:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4031+point (1327/200) 4096 4032)/2 = (7526001:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4031
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_251
