import WR2ClassicalCPayments
import WR2ClassicalCPoints062
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_062 (j : Fin 16) : cPayment (16*62+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*62+j.val)+point (1327/200) 4096 (16*62+j.val+1))/2) := by
  fin_cases j
  · change cPayment 992 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 992+point (1327/200) 4096 993)/2)
    have hp : cPayment 992 = (81861605652:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 992+point (1327/200) 4096 993)/2 = (864579:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_992
  · change cPayment 993 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 993+point (1327/200) 4096 994)/2)
    have hp : cPayment 993 = (81873611676:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 993+point (1327/200) 4096 994)/2 = (4323949:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_993
  · change cPayment 994 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 994+point (1327/200) 4096 995)/2)
    have hp : cPayment 994 = (81885539619:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 994+point (1327/200) 4096 995)/2 = (4325003:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_994
  · change cPayment 995 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 995+point (1327/200) 4096 996)/2)
    have hp : cPayment 995 = (81897389601:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 995+point (1327/200) 4096 996)/2 = (4326057:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_995
  · change cPayment 996 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 996+point (1327/200) 4096 997)/2)
    have hp : cPayment 996 = (81909161742:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 996+point (1327/200) 4096 997)/2 = (4327111:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_996
  · change cPayment 997 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 997+point (1327/200) 4096 998)/2)
    have hp : cPayment 997 = (81920856161:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 997+point (1327/200) 4096 998)/2 = (865633:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_997
  · change cPayment 998 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 998+point (1327/200) 4096 999)/2)
    have hp : cPayment 998 = (81932472978:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 998+point (1327/200) 4096 999)/2 = (4329219:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_998
  · change cPayment 999 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 999+point (1327/200) 4096 1000)/2)
    have hp : cPayment 999 = (81944012312:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 999+point (1327/200) 4096 1000)/2 = (4330273:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_999
  · change cPayment 1000 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1000+point (1327/200) 4096 1001)/2)
    have hp : cPayment 1000 = (81955474281:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1000+point (1327/200) 4096 1001)/2 = (4331327:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1000
  · change cPayment 1001 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1001+point (1327/200) 4096 1002)/2)
    have hp : cPayment 1001 = (81966859005:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1001+point (1327/200) 4096 1002)/2 = (4332381:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1001
  · change cPayment 1002 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1002+point (1327/200) 4096 1003)/2)
    have hp : cPayment 1002 = (81978166602:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1002+point (1327/200) 4096 1003)/2 = (866687:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1002
  · change cPayment 1003 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1003+point (1327/200) 4096 1004)/2)
    have hp : cPayment 1003 = (81989397190:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1003+point (1327/200) 4096 1004)/2 = (4334489:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1003
  · change cPayment 1004 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1004+point (1327/200) 4096 1005)/2)
    have hp : cPayment 1004 = (82000550888:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1004+point (1327/200) 4096 1005)/2 = (4335543:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1004
  · change cPayment 1005 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1005+point (1327/200) 4096 1006)/2)
    have hp : cPayment 1005 = (82011627813:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1005+point (1327/200) 4096 1006)/2 = (4336597:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1005
  · change cPayment 1006 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1006+point (1327/200) 4096 1007)/2)
    have hp : cPayment 1006 = (82022628084:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1006+point (1327/200) 4096 1007)/2 = (4337651:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1006
  · change cPayment 1007 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1007+point (1327/200) 4096 1008)/2)
    have hp : cPayment 1007 = (82033551817:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1007+point (1327/200) 4096 1008)/2 = (867741:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1007
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_062
