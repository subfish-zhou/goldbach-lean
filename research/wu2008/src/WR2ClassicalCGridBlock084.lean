import WR2ClassicalCPayments
import WR2ClassicalCPoints084
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_084 (j : Fin 16) : cPayment (16*84+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*84+j.val)+point (1327/200) 4096 (16*84+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1344 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1344+point (1327/200) 4096 1345)/2)
    have hp : cPayment 1344 = (82022462903:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1344+point (1327/200) 4096 1345)/2 = (4693903:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1344
  · change cPayment 1345 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1345+point (1327/200) 4096 1346)/2)
    have hp : cPayment 1345 = (82013212914:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1345+point (1327/200) 4096 1346)/2 = (4694957:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1345
  · change cPayment 1346 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1346+point (1327/200) 4096 1347)/2)
    have hp : cPayment 1346 = (82003917423:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1346+point (1327/200) 4096 1347)/2 = (4696011:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1346
  · change cPayment 1347 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1347+point (1327/200) 4096 1348)/2)
    have hp : cPayment 1347 = (81994576500:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1347+point (1327/200) 4096 1348)/2 = (939413:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1347
  · change cPayment 1348 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1348+point (1327/200) 4096 1349)/2)
    have hp : cPayment 1348 = (81985190215:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1348+point (1327/200) 4096 1349)/2 = (4698119:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1348
  · change cPayment 1349 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1349+point (1327/200) 4096 1350)/2)
    have hp : cPayment 1349 = (81975758638:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1349+point (1327/200) 4096 1350)/2 = (4699173:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1349
  · change cPayment 1350 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1350+point (1327/200) 4096 1351)/2)
    have hp : cPayment 1350 = (81966281839:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1350+point (1327/200) 4096 1351)/2 = (4700227:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1350
  · change cPayment 1351 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1351+point (1327/200) 4096 1352)/2)
    have hp : cPayment 1351 = (81956759888:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1351+point (1327/200) 4096 1352)/2 = (4701281:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1351
  · change cPayment 1352 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1352+point (1327/200) 4096 1353)/2)
    have hp : cPayment 1352 = (81947192853:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1352+point (1327/200) 4096 1353)/2 = (940467:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1352
  · change cPayment 1353 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1353+point (1327/200) 4096 1354)/2)
    have hp : cPayment 1353 = (81937580806:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1353+point (1327/200) 4096 1354)/2 = (4703389:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1353
  · change cPayment 1354 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1354+point (1327/200) 4096 1355)/2)
    have hp : cPayment 1354 = (81927923814:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1354+point (1327/200) 4096 1355)/2 = (4704443:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1354
  · change cPayment 1355 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1355+point (1327/200) 4096 1356)/2)
    have hp : cPayment 1355 = (81918221947:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1355+point (1327/200) 4096 1356)/2 = (4705497:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1355
  · change cPayment 1356 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1356+point (1327/200) 4096 1357)/2)
    have hp : cPayment 1356 = (81908475275:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1356+point (1327/200) 4096 1357)/2 = (4706551:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1356
  · change cPayment 1357 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1357+point (1327/200) 4096 1358)/2)
    have hp : cPayment 1357 = (81898683867:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1357+point (1327/200) 4096 1358)/2 = (941521:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1357
  · change cPayment 1358 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1358+point (1327/200) 4096 1359)/2)
    have hp : cPayment 1358 = (81888847790:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1358+point (1327/200) 4096 1359)/2 = (4708659:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1358
  · change cPayment 1359 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1359+point (1327/200) 4096 1360)/2)
    have hp : cPayment 1359 = (81878967115:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1359+point (1327/200) 4096 1360)/2 = (4709713:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1359
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_084
