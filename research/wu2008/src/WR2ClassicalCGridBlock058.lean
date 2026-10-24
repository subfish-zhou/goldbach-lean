import WR2ClassicalCPayments
import WR2ClassicalCPoints058
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_058 (j : Fin 16) : cPayment (16*58+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*58+j.val)+point (1327/200) 4096 (16*58+j.val+1))/2) := by
  fin_cases j
  · change cPayment 928 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 928+point (1327/200) 4096 929)/2)
    have hp : cPayment 928 = (80925179058:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 928+point (1327/200) 4096 929)/2 = (4255439:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_928
  · change cPayment 929 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 929+point (1327/200) 4096 930)/2)
    have hp : cPayment 929 = (80942440471:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 929+point (1327/200) 4096 930)/2 = (4256493:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_929
  · change cPayment 930 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 930+point (1327/200) 4096 931)/2)
    have hp : cPayment 930 = (80959615723:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 930+point (1327/200) 4096 931)/2 = (4257547:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_930
  · change cPayment 931 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 931+point (1327/200) 4096 932)/2)
    have hp : cPayment 931 = (80976704947:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 931+point (1327/200) 4096 932)/2 = (4258601:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_931
  · change cPayment 932 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 932+point (1327/200) 4096 933)/2)
    have hp : cPayment 932 = (80993708275:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 932+point (1327/200) 4096 933)/2 = (851931:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_932
  · change cPayment 933 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 933+point (1327/200) 4096 934)/2)
    have hp : cPayment 933 = (81010625840:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 933+point (1327/200) 4096 934)/2 = (4260709:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_933
  · change cPayment 934 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 934+point (1327/200) 4096 935)/2)
    have hp : cPayment 934 = (81027457773:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 934+point (1327/200) 4096 935)/2 = (4261763:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_934
  · change cPayment 935 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 935+point (1327/200) 4096 936)/2)
    have hp : cPayment 935 = (81044204206:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 935+point (1327/200) 4096 936)/2 = (4262817:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_935
  · change cPayment 936 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 936+point (1327/200) 4096 937)/2)
    have hp : cPayment 936 = (81060865271:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 936+point (1327/200) 4096 937)/2 = (4263871:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_936
  · change cPayment 937 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 937+point (1327/200) 4096 938)/2)
    have hp : cPayment 937 = (81077441100:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 937+point (1327/200) 4096 938)/2 = (170597:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_937
  · change cPayment 938 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 938+point (1327/200) 4096 939)/2)
    have hp : cPayment 938 = (81093931824:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 938+point (1327/200) 4096 939)/2 = (4265979:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_938
  · change cPayment 939 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 939+point (1327/200) 4096 940)/2)
    have hp : cPayment 939 = (81110337573:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 939+point (1327/200) 4096 940)/2 = (4267033:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_939
  · change cPayment 940 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 940+point (1327/200) 4096 941)/2)
    have hp : cPayment 940 = (81126658478:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 940+point (1327/200) 4096 941)/2 = (4268087:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_940
  · change cPayment 941 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 941+point (1327/200) 4096 942)/2)
    have hp : cPayment 941 = (81142894671:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 941+point (1327/200) 4096 942)/2 = (4269141:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_941
  · change cPayment 942 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 942+point (1327/200) 4096 943)/2)
    have hp : cPayment 942 = (81159046281:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 942+point (1327/200) 4096 943)/2 = (854039:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_942
  · change cPayment 943 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 943+point (1327/200) 4096 944)/2)
    have hp : cPayment 943 = (81175113439:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 943+point (1327/200) 4096 944)/2 = (4271249:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_943
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_058
