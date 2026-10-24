import WR2ClassicalCPayments
import WR2ClassicalCPoints063
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_063 (j : Fin 16) : cPayment (16*63+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*63+j.val)+point (1327/200) 4096 (16*63+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1008 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1008+point (1327/200) 4096 1009)/2)
    have hp : cPayment 1008 = (82044399131:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1008+point (1327/200) 4096 1009)/2 = (4339759:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1008
  · change cPayment 1009 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1009+point (1327/200) 4096 1010)/2)
    have hp : cPayment 1009 = (82055170143:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1009+point (1327/200) 4096 1010)/2 = (4340813:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1009
  · change cPayment 1010 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1010+point (1327/200) 4096 1011)/2)
    have hp : cPayment 1010 = (82065864969:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1010+point (1327/200) 4096 1011)/2 = (4341867:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1010
  · change cPayment 1011 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1011+point (1327/200) 4096 1012)/2)
    have hp : cPayment 1011 = (82076483726:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1011+point (1327/200) 4096 1012)/2 = (4342921:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1011
  · change cPayment 1012 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1012+point (1327/200) 4096 1013)/2)
    have hp : cPayment 1012 = (82087026532:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1012+point (1327/200) 4096 1013)/2 = (173759:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1012
  · change cPayment 1013 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1013+point (1327/200) 4096 1014)/2)
    have hp : cPayment 1013 = (82097493502:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1013+point (1327/200) 4096 1014)/2 = (4345029:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1013
  · change cPayment 1014 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1014+point (1327/200) 4096 1015)/2)
    have hp : cPayment 1014 = (82107884754:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1014+point (1327/200) 4096 1015)/2 = (4346083:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1014
  · change cPayment 1015 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1015+point (1327/200) 4096 1016)/2)
    have hp : cPayment 1015 = (82118200403:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1015+point (1327/200) 4096 1016)/2 = (4347137:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1015
  · change cPayment 1016 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1016+point (1327/200) 4096 1017)/2)
    have hp : cPayment 1016 = (82128440565:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1016+point (1327/200) 4096 1017)/2 = (4348191:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1016
  · change cPayment 1017 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1017+point (1327/200) 4096 1018)/2)
    have hp : cPayment 1017 = (82138605356:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1017+point (1327/200) 4096 1018)/2 = (869849:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1017
  · change cPayment 1018 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1018+point (1327/200) 4096 1019)/2)
    have hp : cPayment 1018 = (82148694891:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1018+point (1327/200) 4096 1019)/2 = (4350299:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1018
  · change cPayment 1019 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1019+point (1327/200) 4096 1020)/2)
    have hp : cPayment 1019 = (82158709287:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1019+point (1327/200) 4096 1020)/2 = (4351353:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1019
  · change cPayment 1020 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1020+point (1327/200) 4096 1021)/2)
    have hp : cPayment 1020 = (82168648657:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1020+point (1327/200) 4096 1021)/2 = (4352407:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1020
  · change cPayment 1021 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1021+point (1327/200) 4096 1022)/2)
    have hp : cPayment 1021 = (82178513118:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1021+point (1327/200) 4096 1022)/2 = (4353461:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1021
  · change cPayment 1022 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1022+point (1327/200) 4096 1023)/2)
    have hp : cPayment 1022 = (82188302784:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1022+point (1327/200) 4096 1023)/2 = (870903:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1022
  · change cPayment 1023 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1023+point (1327/200) 4096 1024)/2)
    have hp : cPayment 1023 = (82198017770:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1023+point (1327/200) 4096 1024)/2 = (4355569:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1023
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_063
