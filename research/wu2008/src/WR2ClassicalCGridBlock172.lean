import WR2ClassicalCPayments
import WR2ClassicalCPoints172
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_172 (j : Fin 16) : cPayment (16*172+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*172+j.val)+point (1327/200) 4096 (16*172+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2752 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2752+point (1327/200) 4096 2753)/2)
    have hp : cPayment 2752 = (45000104117:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2752+point (1327/200) 4096 2753)/2 = (1235587:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2752
  · change cPayment 2753 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2753+point (1327/200) 4096 2754)/2)
    have hp : cPayment 2753 = (44966233323:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2753+point (1327/200) 4096 2754)/2 = (6178989:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2753
  · change cPayment 2754 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2754+point (1327/200) 4096 2755)/2)
    have hp : cPayment 2754 = (44932360024:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2754+point (1327/200) 4096 2755)/2 = (6180043:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2754
  · change cPayment 2755 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2755+point (1327/200) 4096 2756)/2)
    have hp : cPayment 2755 = (44898484230:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2755+point (1327/200) 4096 2756)/2 = (6181097:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2755
  · change cPayment 2756 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2756+point (1327/200) 4096 2757)/2)
    have hp : cPayment 2756 = (44864605951:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2756+point (1327/200) 4096 2757)/2 = (6182151:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2756
  · change cPayment 2757 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2757+point (1327/200) 4096 2758)/2)
    have hp : cPayment 2757 = (44830725197:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2757+point (1327/200) 4096 2758)/2 = (1236641:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2757
  · change cPayment 2758 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2758+point (1327/200) 4096 2759)/2)
    have hp : cPayment 2758 = (44796841979:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2758+point (1327/200) 4096 2759)/2 = (6184259:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2758
  · change cPayment 2759 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2759+point (1327/200) 4096 2760)/2)
    have hp : cPayment 2759 = (44762956306:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2759+point (1327/200) 4096 2760)/2 = (6185313:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2759
  · change cPayment 2760 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2760+point (1327/200) 4096 2761)/2)
    have hp : cPayment 2760 = (44729068188:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2760+point (1327/200) 4096 2761)/2 = (6186367:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2760
  · change cPayment 2761 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2761+point (1327/200) 4096 2762)/2)
    have hp : cPayment 2761 = (44695177636:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2761+point (1327/200) 4096 2762)/2 = (6187421:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2761
  · change cPayment 2762 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2762+point (1327/200) 4096 2763)/2)
    have hp : cPayment 2762 = (44661284660:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2762+point (1327/200) 4096 2763)/2 = (247539:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2762
  · change cPayment 2763 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2763+point (1327/200) 4096 2764)/2)
    have hp : cPayment 2763 = (44627389270:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2763+point (1327/200) 4096 2764)/2 = (6189529:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2763
  · change cPayment 2764 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2764+point (1327/200) 4096 2765)/2)
    have hp : cPayment 2764 = (44593491475:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2764+point (1327/200) 4096 2765)/2 = (6190583:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2764
  · change cPayment 2765 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2765+point (1327/200) 4096 2766)/2)
    have hp : cPayment 2765 = (44559591287:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2765+point (1327/200) 4096 2766)/2 = (6191637:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2765
  · change cPayment 2766 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2766+point (1327/200) 4096 2767)/2)
    have hp : cPayment 2766 = (44525688715:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2766+point (1327/200) 4096 2767)/2 = (6192691:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2766
  · change cPayment 2767 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2767+point (1327/200) 4096 2768)/2)
    have hp : cPayment 2767 = (44491783769:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2767+point (1327/200) 4096 2768)/2 = (1238749:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2767
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_172
