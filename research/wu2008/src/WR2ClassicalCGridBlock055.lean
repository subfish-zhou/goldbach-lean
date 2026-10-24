import WR2ClassicalCPayments
import WR2ClassicalCPoints055
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_055 (j : Fin 16) : cPayment (16*55+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*55+j.val)+point (1327/200) 4096 (16*55+j.val+1))/2) := by
  fin_cases j
  · change cPayment 880 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 880+point (1327/200) 4096 881)/2)
    have hp : cPayment 880 = (79992650970:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 880+point (1327/200) 4096 881)/2 = (4204847:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_880
  · change cPayment 881 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 881+point (1327/200) 4096 882)/2)
    have hp : cPayment 881 = (80014208421:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 881+point (1327/200) 4096 882)/2 = (4205901:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_881
  · change cPayment 882 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 882+point (1327/200) 4096 883)/2)
    have hp : cPayment 882 = (80035673085:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 882+point (1327/200) 4096 883)/2 = (841391:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_882
  · change cPayment 883 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 883+point (1327/200) 4096 884)/2)
    have hp : cPayment 883 = (80057045104:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 883+point (1327/200) 4096 884)/2 = (4208009:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_883
  · change cPayment 884 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 884+point (1327/200) 4096 885)/2)
    have hp : cPayment 884 = (80078324622:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 884+point (1327/200) 4096 885)/2 = (4209063:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_884
  · change cPayment 885 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 885+point (1327/200) 4096 886)/2)
    have hp : cPayment 885 = (80099511781:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 885+point (1327/200) 4096 886)/2 = (4210117:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_885
  · change cPayment 886 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 886+point (1327/200) 4096 887)/2)
    have hp : cPayment 886 = (80120606725:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 886+point (1327/200) 4096 887)/2 = (4211171:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_886
  · change cPayment 887 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 887+point (1327/200) 4096 888)/2)
    have hp : cPayment 887 = (80141609595:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 887+point (1327/200) 4096 888)/2 = (168489:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_887
  · change cPayment 888 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 888+point (1327/200) 4096 889)/2)
    have hp : cPayment 888 = (80162520534:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 888+point (1327/200) 4096 889)/2 = (4213279:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_888
  · change cPayment 889 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 889+point (1327/200) 4096 890)/2)
    have hp : cPayment 889 = (80183339683:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 889+point (1327/200) 4096 890)/2 = (4214333:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_889
  · change cPayment 890 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 890+point (1327/200) 4096 891)/2)
    have hp : cPayment 890 = (80204067186:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 890+point (1327/200) 4096 891)/2 = (4215387:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_890
  · change cPayment 891 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 891+point (1327/200) 4096 892)/2)
    have hp : cPayment 891 = (80224703182:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 891+point (1327/200) 4096 892)/2 = (4216441:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_891
  · change cPayment 892 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 892+point (1327/200) 4096 893)/2)
    have hp : cPayment 892 = (80245247813:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 892+point (1327/200) 4096 893)/2 = (843499:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_892
  · change cPayment 893 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 893+point (1327/200) 4096 894)/2)
    have hp : cPayment 893 = (80265701222:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 893+point (1327/200) 4096 894)/2 = (4218549:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_893
  · change cPayment 894 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 894+point (1327/200) 4096 895)/2)
    have hp : cPayment 894 = (80286063547:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 894+point (1327/200) 4096 895)/2 = (4219603:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_894
  · change cPayment 895 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 895+point (1327/200) 4096 896)/2)
    have hp : cPayment 895 = (80306334930:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 895+point (1327/200) 4096 896)/2 = (4220657:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_895
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_055
