import WR2ClassicalCPayments
import WR2ClassicalCPoints248
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_248 (j : Fin 16) : cPayment (16*248+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*248+j.val)+point (1327/200) 4096 (16*248+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3968 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3968+point (1327/200) 4096 3969)/2)
    have hp : cPayment 3968 = (4082888082:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3968+point (1327/200) 4096 3969)/2 = (7459599:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3968
  · change cPayment 3969 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3969+point (1327/200) 4096 3970)/2)
    have hp : cPayment 3969 = (4050637493:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3969+point (1327/200) 4096 3970)/2 = (7460653:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3969
  · change cPayment 3970 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3970+point (1327/200) 4096 3971)/2)
    have hp : cPayment 3970 = (4018390438:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3970+point (1327/200) 4096 3971)/2 = (7461707:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3970
  · change cPayment 3971 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3971+point (1327/200) 4096 3972)/2)
    have hp : cPayment 3971 = (3986146917:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3971+point (1327/200) 4096 3972)/2 = (7462761:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3971
  · change cPayment 3972 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3972+point (1327/200) 4096 3973)/2)
    have hp : cPayment 3972 = (3953906934:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3972+point (1327/200) 4096 3973)/2 = (1492763:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3972
  · change cPayment 3973 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3973+point (1327/200) 4096 3974)/2)
    have hp : cPayment 3973 = (3921670489:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3973+point (1327/200) 4096 3974)/2 = (7464869:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3973
  · change cPayment 3974 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3974+point (1327/200) 4096 3975)/2)
    have hp : cPayment 3974 = (3889437584:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3974+point (1327/200) 4096 3975)/2 = (7465923:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3974
  · change cPayment 3975 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3975+point (1327/200) 4096 3976)/2)
    have hp : cPayment 3975 = (3857208222:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3975+point (1327/200) 4096 3976)/2 = (7466977:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3975
  · change cPayment 3976 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3976+point (1327/200) 4096 3977)/2)
    have hp : cPayment 3976 = (3824982403:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3976+point (1327/200) 4096 3977)/2 = (7468031:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3976
  · change cPayment 3977 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3977+point (1327/200) 4096 3978)/2)
    have hp : cPayment 3977 = (3792760131:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3977+point (1327/200) 4096 3978)/2 = (1493817:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3977
  · change cPayment 3978 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3978+point (1327/200) 4096 3979)/2)
    have hp : cPayment 3978 = (3760541405:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3978+point (1327/200) 4096 3979)/2 = (7470139:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3978
  · change cPayment 3979 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3979+point (1327/200) 4096 3980)/2)
    have hp : cPayment 3979 = (3728326229:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3979+point (1327/200) 4096 3980)/2 = (7471193:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3979
  · change cPayment 3980 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3980+point (1327/200) 4096 3981)/2)
    have hp : cPayment 3980 = (3696114604:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3980+point (1327/200) 4096 3981)/2 = (7472247:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3980
  · change cPayment 3981 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3981+point (1327/200) 4096 3982)/2)
    have hp : cPayment 3981 = (3663906531:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3981+point (1327/200) 4096 3982)/2 = (7473301:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3981
  · change cPayment 3982 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3982+point (1327/200) 4096 3983)/2)
    have hp : cPayment 3982 = (3631702013:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3982+point (1327/200) 4096 3983)/2 = (1494871:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3982
  · change cPayment 3983 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3983+point (1327/200) 4096 3984)/2)
    have hp : cPayment 3983 = (3599501051:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3983+point (1327/200) 4096 3984)/2 = (7475409:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3983
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_248
