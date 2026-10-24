import WR2ClassicalCPayments
import WR2ClassicalCPoints061
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_061 (j : Fin 16) : cPayment (16*61+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*61+j.val)+point (1327/200) 4096 (16*61+j.val+1))/2) := by
  fin_cases j
  · change cPayment 976 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 976+point (1327/200) 4096 977)/2)
    have hp : cPayment 976 = (81658791765:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 976+point (1327/200) 4096 977)/2 = (4306031:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_976
  · change cPayment 977 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 977+point (1327/200) 4096 978)/2)
    have hp : cPayment 977 = (81672063535:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 977+point (1327/200) 4096 978)/2 = (861417:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_977
  · change cPayment 978 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 978+point (1327/200) 4096 979)/2)
    have hp : cPayment 978 = (81685255281:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 978+point (1327/200) 4096 979)/2 = (4308139:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_978
  · change cPayment 979 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 979+point (1327/200) 4096 980)/2)
    have hp : cPayment 979 = (81698367126:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 979+point (1327/200) 4096 980)/2 = (4309193:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_979
  · change cPayment 980 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 980+point (1327/200) 4096 981)/2)
    have hp : cPayment 980 = (81711399191:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 980+point (1327/200) 4096 981)/2 = (4310247:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_980
  · change cPayment 981 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 981+point (1327/200) 4096 982)/2)
    have hp : cPayment 981 = (81724351601:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 981+point (1327/200) 4096 982)/2 = (4311301:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_981
  · change cPayment 982 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 982+point (1327/200) 4096 983)/2)
    have hp : cPayment 982 = (81737224477:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 982+point (1327/200) 4096 983)/2 = (862471:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_982
  · change cPayment 983 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 983+point (1327/200) 4096 984)/2)
    have hp : cPayment 983 = (81750017941:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 983+point (1327/200) 4096 984)/2 = (4313409:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_983
  · change cPayment 984 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 984+point (1327/200) 4096 985)/2)
    have hp : cPayment 984 = (81762732115:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 984+point (1327/200) 4096 985)/2 = (4314463:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_984
  · change cPayment 985 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 985+point (1327/200) 4096 986)/2)
    have hp : cPayment 985 = (81775367122:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 985+point (1327/200) 4096 986)/2 = (4315517:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_985
  · change cPayment 986 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 986+point (1327/200) 4096 987)/2)
    have hp : cPayment 986 = (81787923082:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 986+point (1327/200) 4096 987)/2 = (4316571:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_986
  · change cPayment 987 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 987+point (1327/200) 4096 988)/2)
    have hp : cPayment 987 = (81800400117:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 987+point (1327/200) 4096 988)/2 = (172705:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_987
  · change cPayment 988 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 988+point (1327/200) 4096 989)/2)
    have hp : cPayment 988 = (81812798348:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 988+point (1327/200) 4096 989)/2 = (4318679:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_988
  · change cPayment 989 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 989+point (1327/200) 4096 990)/2)
    have hp : cPayment 989 = (81825117896:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 989+point (1327/200) 4096 990)/2 = (4319733:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_989
  · change cPayment 990 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 990+point (1327/200) 4096 991)/2)
    have hp : cPayment 990 = (81837358883:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 990+point (1327/200) 4096 991)/2 = (4320787:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_990
  · change cPayment 991 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 991+point (1327/200) 4096 992)/2)
    have hp : cPayment 991 = (81849521428:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 991+point (1327/200) 4096 992)/2 = (4321841:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_991
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_061
