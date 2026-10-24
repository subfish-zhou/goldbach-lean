import WR2ClassicalCPayments
import WR2ClassicalCPoints188
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_188 (j : Fin 16) : cPayment (16*188+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*188+j.val)+point (1327/200) 4096 (16*188+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3008 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3008+point (1327/200) 4096 3009)/2)
    have hp : cPayment 3008 = (36273349134:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3008+point (1327/200) 4096 3009)/2 = (6447759:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3008
  · change cPayment 3009 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3009+point (1327/200) 4096 3010)/2)
    have hp : cPayment 3009 = (36239135076:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3009+point (1327/200) 4096 3010)/2 = (6448813:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3009
  · change cPayment 3010 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3010+point (1327/200) 4096 3011)/2)
    have hp : cPayment 3010 = (36204920724:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3010+point (1327/200) 4096 3011)/2 = (6449867:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3010
  · change cPayment 3011 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3011+point (1327/200) 4096 3012)/2)
    have hp : cPayment 3011 = (36170706086:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3011+point (1327/200) 4096 3012)/2 = (6450921:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3011
  · change cPayment 3012 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3012+point (1327/200) 4096 3013)/2)
    have hp : cPayment 3012 = (36136491169:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3012+point (1327/200) 4096 3013)/2 = (258079:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3012
  · change cPayment 3013 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3013+point (1327/200) 4096 3014)/2)
    have hp : cPayment 3013 = (36102275981:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3013+point (1327/200) 4096 3014)/2 = (6453029:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3013
  · change cPayment 3014 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3014+point (1327/200) 4096 3015)/2)
    have hp : cPayment 3014 = (36068060528:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3014+point (1327/200) 4096 3015)/2 = (6454083:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3014
  · change cPayment 3015 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3015+point (1327/200) 4096 3016)/2)
    have hp : cPayment 3015 = (36033844818:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3015+point (1327/200) 4096 3016)/2 = (6455137:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3015
  · change cPayment 3016 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3016+point (1327/200) 4096 3017)/2)
    have hp : cPayment 3016 = (35999628857:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3016+point (1327/200) 4096 3017)/2 = (6456191:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3016
  · change cPayment 3017 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3017+point (1327/200) 4096 3018)/2)
    have hp : cPayment 3017 = (35965412654:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3017+point (1327/200) 4096 3018)/2 = (1291449:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3017
  · change cPayment 3018 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3018+point (1327/200) 4096 3019)/2)
    have hp : cPayment 3018 = (35931196215:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3018+point (1327/200) 4096 3019)/2 = (6458299:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3018
  · change cPayment 3019 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3019+point (1327/200) 4096 3020)/2)
    have hp : cPayment 3019 = (35896979547:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3019+point (1327/200) 4096 3020)/2 = (6459353:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3019
  · change cPayment 3020 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3020+point (1327/200) 4096 3021)/2)
    have hp : cPayment 3020 = (35862762658:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3020+point (1327/200) 4096 3021)/2 = (6460407:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3020
  · change cPayment 3021 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3021+point (1327/200) 4096 3022)/2)
    have hp : cPayment 3021 = (35828545555:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3021+point (1327/200) 4096 3022)/2 = (6461461:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3021
  · change cPayment 3022 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3022+point (1327/200) 4096 3023)/2)
    have hp : cPayment 3022 = (35794328244:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3022+point (1327/200) 4096 3023)/2 = (1292503:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3022
  · change cPayment 3023 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3023+point (1327/200) 4096 3024)/2)
    have hp : cPayment 3023 = (35760110734:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3023+point (1327/200) 4096 3024)/2 = (6463569:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3023
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_188
