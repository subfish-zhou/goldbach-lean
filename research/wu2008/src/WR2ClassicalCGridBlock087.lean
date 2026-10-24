import WR2ClassicalCPayments
import WR2ClassicalCPoints087
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_087 (j : Fin 16) : cPayment (16*87+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*87+j.val)+point (1327/200) 4096 (16*87+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1392 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1392+point (1327/200) 4096 1393)/2)
    have hp : cPayment 1392 = (81528329727:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1392+point (1327/200) 4096 1393)/2 = (948899:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1392
  · change cPayment 1393 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1393+point (1327/200) 4096 1394)/2)
    have hp : cPayment 1393 = (81516972952:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1393+point (1327/200) 4096 1394)/2 = (4745549:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1393
  · change cPayment 1394 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1394+point (1327/200) 4096 1395)/2)
    have hp : cPayment 1394 = (81505573927:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1394+point (1327/200) 4096 1395)/2 = (4746603:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1394
  · change cPayment 1395 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1395+point (1327/200) 4096 1396)/2)
    have hp : cPayment 1395 = (81494132715:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1395+point (1327/200) 4096 1396)/2 = (4747657:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1395
  · change cPayment 1396 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1396+point (1327/200) 4096 1397)/2)
    have hp : cPayment 1396 = (81482649382:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1396+point (1327/200) 4096 1397)/2 = (4748711:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1396
  · change cPayment 1397 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1397+point (1327/200) 4096 1398)/2)
    have hp : cPayment 1397 = (81471123994:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1397+point (1327/200) 4096 1398)/2 = (949953:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1397
  · change cPayment 1398 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1398+point (1327/200) 4096 1399)/2)
    have hp : cPayment 1398 = (81459556615:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1398+point (1327/200) 4096 1399)/2 = (4750819:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1398
  · change cPayment 1399 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1399+point (1327/200) 4096 1400)/2)
    have hp : cPayment 1399 = (81447947310:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1399+point (1327/200) 4096 1400)/2 = (4751873:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1399
  · change cPayment 1400 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1400+point (1327/200) 4096 1401)/2)
    have hp : cPayment 1400 = (81436296145:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1400+point (1327/200) 4096 1401)/2 = (4752927:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1400
  · change cPayment 1401 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1401+point (1327/200) 4096 1402)/2)
    have hp : cPayment 1401 = (81424603183:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1401+point (1327/200) 4096 1402)/2 = (4753981:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1401
  · change cPayment 1402 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1402+point (1327/200) 4096 1403)/2)
    have hp : cPayment 1402 = (81412868490:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1402+point (1327/200) 4096 1403)/2 = (951007:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1402
  · change cPayment 1403 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1403+point (1327/200) 4096 1404)/2)
    have hp : cPayment 1403 = (81401092130:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1403+point (1327/200) 4096 1404)/2 = (4756089:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1403
  · change cPayment 1404 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1404+point (1327/200) 4096 1405)/2)
    have hp : cPayment 1404 = (81389274167:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1404+point (1327/200) 4096 1405)/2 = (4757143:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1404
  · change cPayment 1405 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1405+point (1327/200) 4096 1406)/2)
    have hp : cPayment 1405 = (81377414667:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1405+point (1327/200) 4096 1406)/2 = (4758197:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1405
  · change cPayment 1406 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1406+point (1327/200) 4096 1407)/2)
    have hp : cPayment 1406 = (81365513692:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1406+point (1327/200) 4096 1407)/2 = (4759251:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1406
  · change cPayment 1407 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1407+point (1327/200) 4096 1408)/2)
    have hp : cPayment 1407 = (81353571308:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1407+point (1327/200) 4096 1408)/2 = (952061:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1407
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_087
