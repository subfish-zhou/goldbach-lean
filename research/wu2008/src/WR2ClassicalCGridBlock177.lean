import WR2ClassicalCPayments
import WR2ClassicalCPoints177
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_177 (j : Fin 16) : cPayment (16*177+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*177+j.val)+point (1327/200) 4096 (16*177+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2832 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2832+point (1327/200) 4096 2833)/2)
    have hp : cPayment 2832 = (42283339912:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2832+point (1327/200) 4096 2833)/2 = (1252451:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2832
  · change cPayment 2833 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2833+point (1327/200) 4096 2834)/2)
    have hp : cPayment 2833 = (42249299805:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2833+point (1327/200) 4096 2834)/2 = (6263309:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2833
  · change cPayment 2834 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2834+point (1327/200) 4096 2835)/2)
    have hp : cPayment 2834 = (42215257968:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2834+point (1327/200) 4096 2835)/2 = (6264363:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2834
  · change cPayment 2835 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2835+point (1327/200) 4096 2836)/2)
    have hp : cPayment 2835 = (42181214407:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2835+point (1327/200) 4096 2836)/2 = (6265417:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2835
  · change cPayment 2836 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2836+point (1327/200) 4096 2837)/2)
    have hp : cPayment 2836 = (42147169134:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2836+point (1327/200) 4096 2837)/2 = (6266471:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2836
  · change cPayment 2837 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2837+point (1327/200) 4096 2838)/2)
    have hp : cPayment 2837 = (42113122157:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2837+point (1327/200) 4096 2838)/2 = (250701:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2837
  · change cPayment 2838 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2838+point (1327/200) 4096 2839)/2)
    have hp : cPayment 2838 = (42079073484:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2838+point (1327/200) 4096 2839)/2 = (6268579:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2838
  · change cPayment 2839 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2839+point (1327/200) 4096 2840)/2)
    have hp : cPayment 2839 = (42045023126:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2839+point (1327/200) 4096 2840)/2 = (6269633:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2839
  · change cPayment 2840 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2840+point (1327/200) 4096 2841)/2)
    have hp : cPayment 2840 = (42010971092:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2840+point (1327/200) 4096 2841)/2 = (6270687:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2840
  · change cPayment 2841 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2841+point (1327/200) 4096 2842)/2)
    have hp : cPayment 2841 = (41976917389:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2841+point (1327/200) 4096 2842)/2 = (6271741:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2841
  · change cPayment 2842 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2842+point (1327/200) 4096 2843)/2)
    have hp : cPayment 2842 = (41942862028:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2842+point (1327/200) 4096 2843)/2 = (1254559:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2842
  · change cPayment 2843 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2843+point (1327/200) 4096 2844)/2)
    have hp : cPayment 2843 = (41908805018:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2843+point (1327/200) 4096 2844)/2 = (6273849:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2843
  · change cPayment 2844 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2844+point (1327/200) 4096 2845)/2)
    have hp : cPayment 2844 = (41874746367:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2844+point (1327/200) 4096 2845)/2 = (6274903:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2844
  · change cPayment 2845 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2845+point (1327/200) 4096 2846)/2)
    have hp : cPayment 2845 = (41840686085:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2845+point (1327/200) 4096 2846)/2 = (6275957:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2845
  · change cPayment 2846 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2846+point (1327/200) 4096 2847)/2)
    have hp : cPayment 2846 = (41806624180:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2846+point (1327/200) 4096 2847)/2 = (6277011:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2846
  · change cPayment 2847 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2847+point (1327/200) 4096 2848)/2)
    have hp : cPayment 2847 = (41772560662:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2847+point (1327/200) 4096 2848)/2 = (1255613:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2847
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_177
