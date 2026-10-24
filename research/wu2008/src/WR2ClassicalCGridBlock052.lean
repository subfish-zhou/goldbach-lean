import WR2ClassicalCPayments
import WR2ClassicalCPoints052
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_052 (j : Fin 16) : cPayment (16*52+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*52+j.val)+point (1327/200) 4096 (16*52+j.val+1))/2) := by
  fin_cases j
  · change cPayment 832 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 832+point (1327/200) 4096 833)/2)
    have hp : cPayment 832 = (78845905949:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 832+point (1327/200) 4096 833)/2 = (830851:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_832
  · change cPayment 833 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 833+point (1327/200) 4096 834)/2)
    have hp : cPayment 833 = (78872090457:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 833+point (1327/200) 4096 834)/2 = (4155309:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_833
  · change cPayment 834 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 834+point (1327/200) 4096 835)/2)
    have hp : cPayment 834 = (78898175015:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 834+point (1327/200) 4096 835)/2 = (4156363:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_834
  · change cPayment 835 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 835+point (1327/200) 4096 836)/2)
    have hp : cPayment 835 = (78924159778:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 835+point (1327/200) 4096 836)/2 = (4157417:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_835
  · change cPayment 836 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 836+point (1327/200) 4096 837)/2)
    have hp : cPayment 836 = (78950044900:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 836+point (1327/200) 4096 837)/2 = (4158471:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_836
  · change cPayment 837 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 837+point (1327/200) 4096 838)/2)
    have hp : cPayment 837 = (78975830537:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 837+point (1327/200) 4096 838)/2 = (166381:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_837
  · change cPayment 838 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 838+point (1327/200) 4096 839)/2)
    have hp : cPayment 838 = (79001516841:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 838+point (1327/200) 4096 839)/2 = (4160579:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_838
  · change cPayment 839 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 839+point (1327/200) 4096 840)/2)
    have hp : cPayment 839 = (79027103968:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 839+point (1327/200) 4096 840)/2 = (4161633:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_839
  · change cPayment 840 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 840+point (1327/200) 4096 841)/2)
    have hp : cPayment 840 = (79052592071:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 840+point (1327/200) 4096 841)/2 = (4162687:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_840
  · change cPayment 841 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 841+point (1327/200) 4096 842)/2)
    have hp : cPayment 841 = (79077981303:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 841+point (1327/200) 4096 842)/2 = (4163741:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_841
  · change cPayment 842 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 842+point (1327/200) 4096 843)/2)
    have hp : cPayment 842 = (79103271819:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 842+point (1327/200) 4096 843)/2 = (832959:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_842
  · change cPayment 843 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 843+point (1327/200) 4096 844)/2)
    have hp : cPayment 843 = (79128463770:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 843+point (1327/200) 4096 844)/2 = (4165849:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_843
  · change cPayment 844 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 844+point (1327/200) 4096 845)/2)
    have hp : cPayment 844 = (79153557309:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 844+point (1327/200) 4096 845)/2 = (4166903:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_844
  · change cPayment 845 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 845+point (1327/200) 4096 846)/2)
    have hp : cPayment 845 = (79178552590:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 845+point (1327/200) 4096 846)/2 = (4167957:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_845
  · change cPayment 846 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 846+point (1327/200) 4096 847)/2)
    have hp : cPayment 846 = (79203449764:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 846+point (1327/200) 4096 847)/2 = (4169011:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_846
  · change cPayment 847 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 847+point (1327/200) 4096 848)/2)
    have hp : cPayment 847 = (79228248983:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 847+point (1327/200) 4096 848)/2 = (834013:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_847
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_052
