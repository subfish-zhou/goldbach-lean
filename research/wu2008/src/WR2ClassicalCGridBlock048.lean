import WR2ClassicalCPayments
import WR2ClassicalCPoints048
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_048 (j : Fin 16) : cPayment (16*48+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*48+j.val)+point (1327/200) 4096 (16*48+j.val+1))/2) := by
  fin_cases j
  · change cPayment 768 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 768+point (1327/200) 4096 769)/2)
    have hp : cPayment 768 = (76954908472:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 768+point (1327/200) 4096 769)/2 = (4086799:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_768
  · change cPayment 769 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 769+point (1327/200) 4096 770)/2)
    have hp : cPayment 769 = (76987824185:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 769+point (1327/200) 4096 770)/2 = (4087853:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_769
  · change cPayment 770 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 770+point (1327/200) 4096 771)/2)
    have hp : cPayment 770 = (77020629477:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 770+point (1327/200) 4096 771)/2 = (4088907:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_770
  · change cPayment 771 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 771+point (1327/200) 4096 772)/2)
    have hp : cPayment 771 = (77053324521:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 771+point (1327/200) 4096 772)/2 = (4089961:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_771
  · change cPayment 772 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 772+point (1327/200) 4096 773)/2)
    have hp : cPayment 772 = (77085909489:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 772+point (1327/200) 4096 773)/2 = (818203:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_772
  · change cPayment 773 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 773+point (1327/200) 4096 774)/2)
    have hp : cPayment 773 = (77118384552:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 773+point (1327/200) 4096 774)/2 = (4092069:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_773
  · change cPayment 774 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 774+point (1327/200) 4096 775)/2)
    have hp : cPayment 774 = (77150749882:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 774+point (1327/200) 4096 775)/2 = (4093123:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_774
  · change cPayment 775 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 775+point (1327/200) 4096 776)/2)
    have hp : cPayment 775 = (77183005650:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 775+point (1327/200) 4096 776)/2 = (4094177:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_775
  · change cPayment 776 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 776+point (1327/200) 4096 777)/2)
    have hp : cPayment 776 = (77215152027:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 776+point (1327/200) 4096 777)/2 = (4095231:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_776
  · change cPayment 777 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 777+point (1327/200) 4096 778)/2)
    have hp : cPayment 777 = (77247189182:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 777+point (1327/200) 4096 778)/2 = (819257:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_777
  · change cPayment 778 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 778+point (1327/200) 4096 779)/2)
    have hp : cPayment 778 = (77279117288:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 778+point (1327/200) 4096 779)/2 = (4097339:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_778
  · change cPayment 779 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 779+point (1327/200) 4096 780)/2)
    have hp : cPayment 779 = (77310936513:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 779+point (1327/200) 4096 780)/2 = (4098393:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_779
  · change cPayment 780 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 780+point (1327/200) 4096 781)/2)
    have hp : cPayment 780 = (77342647028:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 780+point (1327/200) 4096 781)/2 = (4099447:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_780
  · change cPayment 781 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 781+point (1327/200) 4096 782)/2)
    have hp : cPayment 781 = (77374249001:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 781+point (1327/200) 4096 782)/2 = (4100501:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_781
  · change cPayment 782 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 782+point (1327/200) 4096 783)/2)
    have hp : cPayment 782 = (77405742602:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 782+point (1327/200) 4096 783)/2 = (820311:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_782
  · change cPayment 783 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 783+point (1327/200) 4096 784)/2)
    have hp : cPayment 783 = (77437128000:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 783+point (1327/200) 4096 784)/2 = (4102609:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_783
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_048
