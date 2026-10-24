import WR2ClassicalCPayments
import WR2ClassicalCPoints083
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_083 (j : Fin 16) : cPayment (16*83+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*83+j.val)+point (1327/200) 4096 (16*83+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1328 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1328+point (1327/200) 4096 1329)/2)
    have hp : cPayment 1328 = (82164216883:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1328+point (1327/200) 4096 1329)/2 = (4677039:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1328
  · change cPayment 1329 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1329+point (1327/200) 4096 1330)/2)
    have hp : cPayment 1329 = (82155704540:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1329+point (1327/200) 4096 1330)/2 = (4678093:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1329
  · change cPayment 1330 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1330+point (1327/200) 4096 1331)/2)
    have hp : cPayment 1330 = (82147145561:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1330+point (1327/200) 4096 1331)/2 = (4679147:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1330
  · change cPayment 1331 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1331+point (1327/200) 4096 1332)/2)
    have hp : cPayment 1331 = (82138540015:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1331+point (1327/200) 4096 1332)/2 = (4680201:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1331
  · change cPayment 1332 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1332+point (1327/200) 4096 1333)/2)
    have hp : cPayment 1332 = (82129887976:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1332+point (1327/200) 4096 1333)/2 = (936251:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1332
  · change cPayment 1333 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1333+point (1327/200) 4096 1334)/2)
    have hp : cPayment 1333 = (82121189513:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1333+point (1327/200) 4096 1334)/2 = (4682309:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1333
  · change cPayment 1334 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1334+point (1327/200) 4096 1335)/2)
    have hp : cPayment 1334 = (82112444700:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1334+point (1327/200) 4096 1335)/2 = (4683363:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1334
  · change cPayment 1335 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1335+point (1327/200) 4096 1336)/2)
    have hp : cPayment 1335 = (82103653607:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1335+point (1327/200) 4096 1336)/2 = (4684417:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1335
  · change cPayment 1336 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1336+point (1327/200) 4096 1337)/2)
    have hp : cPayment 1336 = (82094816306:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1336+point (1327/200) 4096 1337)/2 = (4685471:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1336
  · change cPayment 1337 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1337+point (1327/200) 4096 1338)/2)
    have hp : cPayment 1337 = (82085932867:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1337+point (1327/200) 4096 1338)/2 = (187461:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1337
  · change cPayment 1338 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1338+point (1327/200) 4096 1339)/2)
    have hp : cPayment 1338 = (82077003362:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1338+point (1327/200) 4096 1339)/2 = (4687579:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1338
  · change cPayment 1339 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1339+point (1327/200) 4096 1340)/2)
    have hp : cPayment 1339 = (82068027862:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1339+point (1327/200) 4096 1340)/2 = (4688633:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1339
  · change cPayment 1340 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1340+point (1327/200) 4096 1341)/2)
    have hp : cPayment 1340 = (82059006437:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1340+point (1327/200) 4096 1341)/2 = (4689687:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1340
  · change cPayment 1341 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1341+point (1327/200) 4096 1342)/2)
    have hp : cPayment 1341 = (82049939158:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1341+point (1327/200) 4096 1342)/2 = (4690741:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1341
  · change cPayment 1342 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1342+point (1327/200) 4096 1343)/2)
    have hp : cPayment 1342 = (82040826096:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1342+point (1327/200) 4096 1343)/2 = (938359:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1342
  · change cPayment 1343 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1343+point (1327/200) 4096 1344)/2)
    have hp : cPayment 1343 = (82031667321:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1343+point (1327/200) 4096 1344)/2 = (4692849:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1343
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_083
