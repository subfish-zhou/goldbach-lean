import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints093
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_093 (j : Fin 16) : upperValue ((point (16*93+j.val)+point ((16*93+j.val)+1))/2) ≤ payment (16*93+j.val) := by
  fin_cases j
  · change upperValue ((point (1488)+point ((1488)+1))/2) ≤ payment (1488)
    have hp : payment 1488 = (989884027264:ℝ)/1000000000000 := rfl
    have hx : (point 1488+point 1489)/2 = (4286179:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1488
  · change upperValue ((point (1489)+point ((1489)+1))/2) ≤ payment (1489)
    have hp : payment 1489 = (987969328486:ℝ)/1000000000000 := rfl
    have hx : (point 1489+point 1490)/2 = (1429411:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1489
  · change upperValue ((point (1490)+point ((1490)+1))/2) ≤ payment (1490)
    have hp : payment 1490 = (986055468593:ℝ)/1000000000000 := rfl
    have hx : (point 1490+point 1491)/2 = (4290287:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1490
  · change upperValue ((point (1491)+point ((1491)+1))/2) ≤ payment (1491)
    have hp : payment 1491 = (984142445558:ℝ)/1000000000000 := rfl
    have hx : (point 1491+point 1492)/2 = (4292341:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1491
  · change upperValue ((point (1492)+point ((1492)+1))/2) ≤ payment (1492)
    have hp : payment 1492 = (982230257357:ℝ)/1000000000000 := rfl
    have hx : (point 1492+point 1493)/2 = (1431465:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1492
  · change upperValue ((point (1493)+point ((1493)+1))/2) ≤ payment (1493)
    have hp : payment 1493 = (980318901968:ℝ)/1000000000000 := rfl
    have hx : (point 1493+point 1494)/2 = (4296449:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1493
  · change upperValue ((point (1494)+point ((1494)+1))/2) ≤ payment (1494)
    have hp : payment 1494 = (978408377372:ℝ)/1000000000000 := rfl
    have hx : (point 1494+point 1495)/2 = (4298503:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1494
  · change upperValue ((point (1495)+point ((1495)+1))/2) ≤ payment (1495)
    have hp : payment 1495 = (976498681554:ℝ)/1000000000000 := rfl
    have hx : (point 1495+point 1496)/2 = (1433519:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1495
  · change upperValue ((point (1496)+point ((1496)+1))/2) ≤ payment (1496)
    have hp : payment 1496 = (974589812502:ℝ)/1000000000000 := rfl
    have hx : (point 1496+point 1497)/2 = (4302611:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1496
  · change upperValue ((point (1497)+point ((1497)+1))/2) ≤ payment (1497)
    have hp : payment 1497 = (972681768205:ℝ)/1000000000000 := rfl
    have hx : (point 1497+point 1498)/2 = (4304665:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1497
  · change upperValue ((point (1498)+point ((1498)+1))/2) ≤ payment (1498)
    have hp : payment 1498 = (970774546658:ℝ)/1000000000000 := rfl
    have hx : (point 1498+point 1499)/2 = (1435573:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1498
  · change upperValue ((point (1499)+point ((1499)+1))/2) ≤ payment (1499)
    have hp : payment 1499 = (968868145856:ℝ)/1000000000000 := rfl
    have hx : (point 1499+point 1500)/2 = (4308773:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1499
  · change upperValue ((point (1500)+point ((1500)+1))/2) ≤ payment (1500)
    have hp : payment 1500 = (966962563799:ℝ)/1000000000000 := rfl
    have hx : (point 1500+point 1501)/2 = (4310827:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1500
  · change upperValue ((point (1501)+point ((1501)+1))/2) ≤ payment (1501)
    have hp : payment 1501 = (965057798490:ℝ)/1000000000000 := rfl
    have hx : (point 1501+point 1502)/2 = (1437627:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1501
  · change upperValue ((point (1502)+point ((1502)+1))/2) ≤ payment (1502)
    have hp : payment 1502 = (963153847933:ℝ)/1000000000000 := rfl
    have hx : (point 1502+point 1503)/2 = (4314935:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1502
  · change upperValue ((point (1503)+point ((1503)+1))/2) ≤ payment (1503)
    have hp : payment 1503 = (961250710137:ℝ)/1000000000000 := rfl
    have hx : (point 1503+point 1504)/2 = (4316989:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1503
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_093
