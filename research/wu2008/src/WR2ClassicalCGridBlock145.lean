import WR2ClassicalCPayments
import WR2ClassicalCPoints145
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_145 (j : Fin 16) : cPayment (16*145+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*145+j.val)+point (1327/200) 4096 (16*145+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2320 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2320+point (1327/200) 4096 2321)/2)
    have hp : cPayment 2320 = (59237699217:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2320+point (1327/200) 4096 2321)/2 = (5722607:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2320
  · change cPayment 2321 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2321+point (1327/200) 4096 2322)/2)
    have hp : cPayment 2321 = (59206076043:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2321+point (1327/200) 4096 2322)/2 = (5723661:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2321
  · change cPayment 2322 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2322+point (1327/200) 4096 2323)/2)
    have hp : cPayment 2322 = (59174444418:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2322+point (1327/200) 4096 2323)/2 = (1144943:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2322
  · change cPayment 2323 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2323+point (1327/200) 4096 2324)/2)
    have hp : cPayment 2323 = (59142804361:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2323+point (1327/200) 4096 2324)/2 = (5725769:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2323
  · change cPayment 2324 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2324+point (1327/200) 4096 2325)/2)
    have hp : cPayment 2324 = (59111155888:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2324+point (1327/200) 4096 2325)/2 = (5726823:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2324
  · change cPayment 2325 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2325+point (1327/200) 4096 2326)/2)
    have hp : cPayment 2325 = (59079499018:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2325+point (1327/200) 4096 2326)/2 = (5727877:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2325
  · change cPayment 2326 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2326+point (1327/200) 4096 2327)/2)
    have hp : cPayment 2326 = (59047833770:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2326+point (1327/200) 4096 2327)/2 = (5728931:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2326
  · change cPayment 2327 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2327+point (1327/200) 4096 2328)/2)
    have hp : cPayment 2327 = (59016160160:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2327+point (1327/200) 4096 2328)/2 = (1145997:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2327
  · change cPayment 2328 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2328+point (1327/200) 4096 2329)/2)
    have hp : cPayment 2328 = (58984478208:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2328+point (1327/200) 4096 2329)/2 = (5731039:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2328
  · change cPayment 2329 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2329+point (1327/200) 4096 2330)/2)
    have hp : cPayment 2329 = (58952787930:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2329+point (1327/200) 4096 2330)/2 = (5732093:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2329
  · change cPayment 2330 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2330+point (1327/200) 4096 2331)/2)
    have hp : cPayment 2330 = (58921089346:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2330+point (1327/200) 4096 2331)/2 = (5733147:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2330
  · change cPayment 2331 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2331+point (1327/200) 4096 2332)/2)
    have hp : cPayment 2331 = (58889382472:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2331+point (1327/200) 4096 2332)/2 = (5734201:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2331
  · change cPayment 2332 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2332+point (1327/200) 4096 2333)/2)
    have hp : cPayment 2332 = (58857667327:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2332+point (1327/200) 4096 2333)/2 = (1147051:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2332
  · change cPayment 2333 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2333+point (1327/200) 4096 2334)/2)
    have hp : cPayment 2333 = (58825943928:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2333+point (1327/200) 4096 2334)/2 = (5736309:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2333
  · change cPayment 2334 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2334+point (1327/200) 4096 2335)/2)
    have hp : cPayment 2334 = (58794212294:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2334+point (1327/200) 4096 2335)/2 = (5737363:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2334
  · change cPayment 2335 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2335+point (1327/200) 4096 2336)/2)
    have hp : cPayment 2335 = (58762472442:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2335+point (1327/200) 4096 2336)/2 = (5738417:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2335
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_145
