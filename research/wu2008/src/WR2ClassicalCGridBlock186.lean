import WR2ClassicalCPayments
import WR2ClassicalCPoints186
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_186 (j : Fin 16) : cPayment (16*186+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*186+j.val)+point (1327/200) 4096 (16*186+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2976 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2976+point (1327/200) 4096 2977)/2)
    have hp : cPayment 2976 = (37368000238:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2976+point (1327/200) 4096 2977)/2 = (6414031:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2976
  · change cPayment 2977 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2977+point (1327/200) 4096 2978)/2)
    have hp : cPayment 2977 = (37333799451:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2977+point (1327/200) 4096 2978)/2 = (1283017:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2977
  · change cPayment 2978 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2978+point (1327/200) 4096 2979)/2)
    have hp : cPayment 2978 = (37299598133:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2978+point (1327/200) 4096 2979)/2 = (6416139:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2978
  · change cPayment 2979 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2979+point (1327/200) 4096 2980)/2)
    have hp : cPayment 2979 = (37265396293:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2979+point (1327/200) 4096 2980)/2 = (6417193:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2979
  · change cPayment 2980 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2980+point (1327/200) 4096 2981)/2)
    have hp : cPayment 2980 = (37231193937:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2980+point (1327/200) 4096 2981)/2 = (6418247:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2980
  · change cPayment 2981 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2981+point (1327/200) 4096 2982)/2)
    have hp : cPayment 2981 = (37196991074:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2981+point (1327/200) 4096 2982)/2 = (6419301:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2981
  · change cPayment 2982 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2982+point (1327/200) 4096 2983)/2)
    have hp : cPayment 2982 = (37162787711:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2982+point (1327/200) 4096 2983)/2 = (1284071:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2982
  · change cPayment 2983 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2983+point (1327/200) 4096 2984)/2)
    have hp : cPayment 2983 = (37128583855:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2983+point (1327/200) 4096 2984)/2 = (6421409:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2983
  · change cPayment 2984 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2984+point (1327/200) 4096 2985)/2)
    have hp : cPayment 2984 = (37094379513:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2984+point (1327/200) 4096 2985)/2 = (6422463:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2984
  · change cPayment 2985 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2985+point (1327/200) 4096 2986)/2)
    have hp : cPayment 2985 = (37060174695:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2985+point (1327/200) 4096 2986)/2 = (6423517:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2985
  · change cPayment 2986 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2986+point (1327/200) 4096 2987)/2)
    have hp : cPayment 2986 = (37025969406:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2986+point (1327/200) 4096 2987)/2 = (6424571:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2986
  · change cPayment 2987 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2987+point (1327/200) 4096 2988)/2)
    have hp : cPayment 2987 = (36991763654:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2987+point (1327/200) 4096 2988)/2 = (257025:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2987
  · change cPayment 2988 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2988+point (1327/200) 4096 2989)/2)
    have hp : cPayment 2988 = (36957557447:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2988+point (1327/200) 4096 2989)/2 = (6426679:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2988
  · change cPayment 2989 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2989+point (1327/200) 4096 2990)/2)
    have hp : cPayment 2989 = (36923350793:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2989+point (1327/200) 4096 2990)/2 = (6427733:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2989
  · change cPayment 2990 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2990+point (1327/200) 4096 2991)/2)
    have hp : cPayment 2990 = (36889143698:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2990+point (1327/200) 4096 2991)/2 = (6428787:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2990
  · change cPayment 2991 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2991+point (1327/200) 4096 2992)/2)
    have hp : cPayment 2991 = (36854936170:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2991+point (1327/200) 4096 2992)/2 = (6429841:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2991
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_186
