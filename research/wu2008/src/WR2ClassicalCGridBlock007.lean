import WR2ClassicalCPayments
import WR2ClassicalCPoints007
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_007 (j : Fin 16) : cPayment (16*7+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*7+j.val)+point (1327/200) 4096 (16*7+j.val+1))/2) := by
  fin_cases j
  · change cPayment 112 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 112+point (1327/200) 4096 113)/2)
    have hp : cPayment 112 = (20450727134:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 112+point (1327/200) 4096 113)/2 = (135815:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_112
  · change cPayment 113 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 113+point (1327/200) 4096 114)/2)
    have hp : cPayment 113 = (20612734884:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 113+point (1327/200) 4096 114)/2 = (3396429:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_113
  · change cPayment 114 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 114+point (1327/200) 4096 115)/2)
    have hp : cPayment 114 = (20774417452:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 114+point (1327/200) 4096 115)/2 = (3397483:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_114
  · change cPayment 115 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 115+point (1327/200) 4096 116)/2)
    have hp : cPayment 115 = (20935775415:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 115+point (1327/200) 4096 116)/2 = (3398537:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_115
  · change cPayment 116 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 116+point (1327/200) 4096 117)/2)
    have hp : cPayment 116 = (21096809346:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 116+point (1327/200) 4096 117)/2 = (3399591:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_116
  · change cPayment 117 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 117+point (1327/200) 4096 118)/2)
    have hp : cPayment 117 = (21257519816:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 117+point (1327/200) 4096 118)/2 = (680129:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_117
  · change cPayment 118 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 118+point (1327/200) 4096 119)/2)
    have hp : cPayment 118 = (21417907397:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 118+point (1327/200) 4096 119)/2 = (3401699:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_118
  · change cPayment 119 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 119+point (1327/200) 4096 120)/2)
    have hp : cPayment 119 = (21577972658:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 119+point (1327/200) 4096 120)/2 = (3402753:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_119
  · change cPayment 120 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 120+point (1327/200) 4096 121)/2)
    have hp : cPayment 120 = (21737716168:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 120+point (1327/200) 4096 121)/2 = (3403807:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_120
  · change cPayment 121 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 121+point (1327/200) 4096 122)/2)
    have hp : cPayment 121 = (21897138495:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 121+point (1327/200) 4096 122)/2 = (3404861:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_121
  · change cPayment 122 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 122+point (1327/200) 4096 123)/2)
    have hp : cPayment 122 = (22056240205:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 122+point (1327/200) 4096 123)/2 = (681183:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_122
  · change cPayment 123 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 123+point (1327/200) 4096 124)/2)
    have hp : cPayment 123 = (22215021863:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 123+point (1327/200) 4096 124)/2 = (3406969:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_123
  · change cPayment 124 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 124+point (1327/200) 4096 125)/2)
    have hp : cPayment 124 = (22373484032:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 124+point (1327/200) 4096 125)/2 = (3408023:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_124
  · change cPayment 125 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 125+point (1327/200) 4096 126)/2)
    have hp : cPayment 125 = (22531627277:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 125+point (1327/200) 4096 126)/2 = (3409077:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_125
  · change cPayment 126 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 126+point (1327/200) 4096 127)/2)
    have hp : cPayment 126 = (22689452158:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 126+point (1327/200) 4096 127)/2 = (3410131:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_126
  · change cPayment 127 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 127+point (1327/200) 4096 128)/2)
    have hp : cPayment 127 = (22846959236:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 127+point (1327/200) 4096 128)/2 = (682237:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_127
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_007
