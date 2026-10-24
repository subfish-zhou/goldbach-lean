import WR2ClassicalCPayments
import WR2ClassicalCPoints051
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_051 (j : Fin 16) : cPayment (16*51+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*51+j.val)+point (1327/200) 4096 (16*51+j.val+1))/2) := by
  fin_cases j
  · change cPayment 816 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 816+point (1327/200) 4096 817)/2)
    have hp : cPayment 816 = (78413233115:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 816+point (1327/200) 4096 817)/2 = (4137391:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_816
  · change cPayment 817 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 817+point (1327/200) 4096 818)/2)
    have hp : cPayment 817 = (78441038117:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 817+point (1327/200) 4096 818)/2 = (827689:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_817
  · change cPayment 818 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 818+point (1327/200) 4096 819)/2)
    have hp : cPayment 818 = (78468740652:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 818+point (1327/200) 4096 819)/2 = (4139499:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_818
  · change cPayment 819 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 819+point (1327/200) 4096 820)/2)
    have hp : cPayment 819 = (78496340882:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 819+point (1327/200) 4096 820)/2 = (4140553:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_819
  · change cPayment 820 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 820+point (1327/200) 4096 821)/2)
    have hp : cPayment 820 = (78523838965:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 820+point (1327/200) 4096 821)/2 = (4141607:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_820
  · change cPayment 821 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 821+point (1327/200) 4096 822)/2)
    have hp : cPayment 821 = (78551235059:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 821+point (1327/200) 4096 822)/2 = (4142661:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_821
  · change cPayment 822 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 822+point (1327/200) 4096 823)/2)
    have hp : cPayment 822 = (78578529323:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 822+point (1327/200) 4096 823)/2 = (828743:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_822
  · change cPayment 823 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 823+point (1327/200) 4096 824)/2)
    have hp : cPayment 823 = (78605721915:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 823+point (1327/200) 4096 824)/2 = (4144769:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_823
  · change cPayment 824 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 824+point (1327/200) 4096 825)/2)
    have hp : cPayment 824 = (78632812992:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 824+point (1327/200) 4096 825)/2 = (4145823:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_824
  · change cPayment 825 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 825+point (1327/200) 4096 826)/2)
    have hp : cPayment 825 = (78659802713:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 825+point (1327/200) 4096 826)/2 = (4146877:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_825
  · change cPayment 826 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 826+point (1327/200) 4096 827)/2)
    have hp : cPayment 826 = (78686691234:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 826+point (1327/200) 4096 827)/2 = (4147931:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_826
  · change cPayment 827 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 827+point (1327/200) 4096 828)/2)
    have hp : cPayment 827 = (78713478713:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 827+point (1327/200) 4096 828)/2 = (829797:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_827
  · change cPayment 828 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 828+point (1327/200) 4096 829)/2)
    have hp : cPayment 828 = (78740165306:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 828+point (1327/200) 4096 829)/2 = (4150039:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_828
  · change cPayment 829 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 829+point (1327/200) 4096 830)/2)
    have hp : cPayment 829 = (78766751170:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 829+point (1327/200) 4096 830)/2 = (4151093:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_829
  · change cPayment 830 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 830+point (1327/200) 4096 831)/2)
    have hp : cPayment 830 = (78793236461:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 830+point (1327/200) 4096 831)/2 = (4152147:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_830
  · change cPayment 831 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 831+point (1327/200) 4096 832)/2)
    have hp : cPayment 831 = (78819621336:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 831+point (1327/200) 4096 832)/2 = (4153201:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_831
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_051
