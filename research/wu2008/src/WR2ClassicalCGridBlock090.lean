import WR2ClassicalCPayments
import WR2ClassicalCPoints090
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_090 (j : Fin 16) : cPayment (16*90+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*90+j.val)+point (1327/200) 4096 (16*90+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1440 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1440+point (1327/200) 4096 1441)/2)
    have hp : cPayment 1440 = (80936656391:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1440+point (1327/200) 4096 1441)/2 = (4795087:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1440
  · change cPayment 1441 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1441+point (1327/200) 4096 1442)/2)
    have hp : cPayment 1441 = (80923343604:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1441+point (1327/200) 4096 1442)/2 = (4796141:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1441
  · change cPayment 1442 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1442+point (1327/200) 4096 1443)/2)
    have hp : cPayment 1442 = (80909991595:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1442+point (1327/200) 4096 1443)/2 = (959439:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1442
  · change cPayment 1443 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1443+point (1327/200) 4096 1444)/2)
    have hp : cPayment 1443 = (80896600426:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1443+point (1327/200) 4096 1444)/2 = (4798249:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1443
  · change cPayment 1444 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1444+point (1327/200) 4096 1445)/2)
    have hp : cPayment 1444 = (80883170157:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1444+point (1327/200) 4096 1445)/2 = (4799303:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1444
  · change cPayment 1445 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1445+point (1327/200) 4096 1446)/2)
    have hp : cPayment 1445 = (80869700849:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1445+point (1327/200) 4096 1446)/2 = (4800357:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1445
  · change cPayment 1446 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1446+point (1327/200) 4096 1447)/2)
    have hp : cPayment 1446 = (80856192562:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1446+point (1327/200) 4096 1447)/2 = (4801411:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1446
  · change cPayment 1447 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1447+point (1327/200) 4096 1448)/2)
    have hp : cPayment 1447 = (80842645358:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1447+point (1327/200) 4096 1448)/2 = (960493:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1447
  · change cPayment 1448 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1448+point (1327/200) 4096 1449)/2)
    have hp : cPayment 1448 = (80829059297:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1448+point (1327/200) 4096 1449)/2 = (4803519:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1448
  · change cPayment 1449 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1449+point (1327/200) 4096 1450)/2)
    have hp : cPayment 1449 = (80815434438:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1449+point (1327/200) 4096 1450)/2 = (4804573:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1449
  · change cPayment 1450 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1450+point (1327/200) 4096 1451)/2)
    have hp : cPayment 1450 = (80801770843:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1450+point (1327/200) 4096 1451)/2 = (4805627:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1450
  · change cPayment 1451 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1451+point (1327/200) 4096 1452)/2)
    have hp : cPayment 1451 = (80788068571:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1451+point (1327/200) 4096 1452)/2 = (4806681:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1451
  · change cPayment 1452 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1452+point (1327/200) 4096 1453)/2)
    have hp : cPayment 1452 = (80774327683:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1452+point (1327/200) 4096 1453)/2 = (961547:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1452
  · change cPayment 1453 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1453+point (1327/200) 4096 1454)/2)
    have hp : cPayment 1453 = (80760548238:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1453+point (1327/200) 4096 1454)/2 = (4808789:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1453
  · change cPayment 1454 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1454+point (1327/200) 4096 1455)/2)
    have hp : cPayment 1454 = (80746730297:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1454+point (1327/200) 4096 1455)/2 = (4809843:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1454
  · change cPayment 1455 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1455+point (1327/200) 4096 1456)/2)
    have hp : cPayment 1455 = (80732873919:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1455+point (1327/200) 4096 1456)/2 = (4810897:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1455
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_090
