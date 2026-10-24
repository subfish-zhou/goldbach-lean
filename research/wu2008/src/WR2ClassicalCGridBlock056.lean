import WR2ClassicalCPayments
import WR2ClassicalCPoints056
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_056 (j : Fin 16) : cPayment (16*56+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*56+j.val)+point (1327/200) 4096 (16*56+j.val+1))/2) := by
  fin_cases j
  · change cPayment 896 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 896+point (1327/200) 4096 897)/2)
    have hp : cPayment 896 = (80326515511:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 896+point (1327/200) 4096 897)/2 = (4221711:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_896
  · change cPayment 897 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 897+point (1327/200) 4096 898)/2)
    have hp : cPayment 897 = (80346605431:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 897+point (1327/200) 4096 898)/2 = (844553:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_897
  · change cPayment 898 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 898+point (1327/200) 4096 899)/2)
    have hp : cPayment 898 = (80366604829:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 898+point (1327/200) 4096 899)/2 = (4223819:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_898
  · change cPayment 899 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 899+point (1327/200) 4096 900)/2)
    have hp : cPayment 899 = (80386513845:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 899+point (1327/200) 4096 900)/2 = (4224873:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_899
  · change cPayment 900 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 900+point (1327/200) 4096 901)/2)
    have hp : cPayment 900 = (80406332618:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 900+point (1327/200) 4096 901)/2 = (4225927:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_900
  · change cPayment 901 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 901+point (1327/200) 4096 902)/2)
    have hp : cPayment 901 = (80426061288:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 901+point (1327/200) 4096 902)/2 = (4226981:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_901
  · change cPayment 902 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 902+point (1327/200) 4096 903)/2)
    have hp : cPayment 902 = (80445699994:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 902+point (1327/200) 4096 903)/2 = (845607:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_902
  · change cPayment 903 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 903+point (1327/200) 4096 904)/2)
    have hp : cPayment 903 = (80465248874:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 903+point (1327/200) 4096 904)/2 = (4229089:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_903
  · change cPayment 904 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 904+point (1327/200) 4096 905)/2)
    have hp : cPayment 904 = (80484708068:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 904+point (1327/200) 4096 905)/2 = (4230143:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_904
  · change cPayment 905 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 905+point (1327/200) 4096 906)/2)
    have hp : cPayment 905 = (80504077713:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 905+point (1327/200) 4096 906)/2 = (4231197:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_905
  · change cPayment 906 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 906+point (1327/200) 4096 907)/2)
    have hp : cPayment 906 = (80523357947:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 906+point (1327/200) 4096 907)/2 = (4232251:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_906
  · change cPayment 907 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 907+point (1327/200) 4096 908)/2)
    have hp : cPayment 907 = (80542548909:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 907+point (1327/200) 4096 908)/2 = (846661:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_907
  · change cPayment 908 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 908+point (1327/200) 4096 909)/2)
    have hp : cPayment 908 = (80561650736:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 908+point (1327/200) 4096 909)/2 = (4234359:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_908
  · change cPayment 909 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 909+point (1327/200) 4096 910)/2)
    have hp : cPayment 909 = (80580663566:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 909+point (1327/200) 4096 910)/2 = (4235413:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_909
  · change cPayment 910 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 910+point (1327/200) 4096 911)/2)
    have hp : cPayment 910 = (80599587536:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 910+point (1327/200) 4096 911)/2 = (4236467:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_910
  · change cPayment 911 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 911+point (1327/200) 4096 912)/2)
    have hp : cPayment 911 = (80618422782:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 911+point (1327/200) 4096 912)/2 = (4237521:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_911
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_056
