import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints094
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_094 (j : Fin 16) : upperValue ((point (16*94+j.val)+point ((16*94+j.val)+1))/2) ≤ payment (16*94+j.val) := by
  fin_cases j
  · change upperValue ((point (1504)+point ((1504)+1))/2) ≤ payment (1504)
    have hp : payment 1504 = (959348383112:ℝ)/1000000000000 := rfl
    have hx : (point 1504+point 1505)/2 = (1439681:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1504
  · change upperValue ((point (1505)+point ((1505)+1))/2) ≤ payment (1505)
    have hp : payment 1505 = (957446864873:ℝ)/1000000000000 := rfl
    have hx : (point 1505+point 1506)/2 = (4321097:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1505
  · change upperValue ((point (1506)+point ((1506)+1))/2) ≤ payment (1506)
    have hp : payment 1506 = (955546153437:ℝ)/1000000000000 := rfl
    have hx : (point 1506+point 1507)/2 = (4323151:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1506
  · change upperValue ((point (1507)+point ((1507)+1))/2) ≤ payment (1507)
    have hp : payment 1507 = (953646246823:ℝ)/1000000000000 := rfl
    have hx : (point 1507+point 1508)/2 = (1441735:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1507
  · change upperValue ((point (1508)+point ((1508)+1))/2) ≤ payment (1508)
    have hp : payment 1508 = (951747143055:ℝ)/1000000000000 := rfl
    have hx : (point 1508+point 1509)/2 = (4327259:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1508
  · change upperValue ((point (1509)+point ((1509)+1))/2) ≤ payment (1509)
    have hp : payment 1509 = (949848840157:ℝ)/1000000000000 := rfl
    have hx : (point 1509+point 1510)/2 = (4329313:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1509
  · change upperValue ((point (1510)+point ((1510)+1))/2) ≤ payment (1510)
    have hp : payment 1510 = (947951336158:ℝ)/1000000000000 := rfl
    have hx : (point 1510+point 1511)/2 = (1443789:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1510
  · change upperValue ((point (1511)+point ((1511)+1))/2) ≤ payment (1511)
    have hp : payment 1511 = (946054629090:ℝ)/1000000000000 := rfl
    have hx : (point 1511+point 1512)/2 = (4333421:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1511
  · change upperValue ((point (1512)+point ((1512)+1))/2) ≤ payment (1512)
    have hp : payment 1512 = (944158716986:ℝ)/1000000000000 := rfl
    have hx : (point 1512+point 1513)/2 = (4335475:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1512
  · change upperValue ((point (1513)+point ((1513)+1))/2) ≤ payment (1513)
    have hp : payment 1513 = (942263597884:ℝ)/1000000000000 := rfl
    have hx : (point 1513+point 1514)/2 = (1445843:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1513
  · change upperValue ((point (1514)+point ((1514)+1))/2) ≤ payment (1514)
    have hp : payment 1514 = (940369269824:ℝ)/1000000000000 := rfl
    have hx : (point 1514+point 1515)/2 = (4339583:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1514
  · change upperValue ((point (1515)+point ((1515)+1))/2) ≤ payment (1515)
    have hp : payment 1515 = (938475730848:ℝ)/1000000000000 := rfl
    have hx : (point 1515+point 1516)/2 = (4341637:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1515
  · change upperValue ((point (1516)+point ((1516)+1))/2) ≤ payment (1516)
    have hp : payment 1516 = (936582979002:ℝ)/1000000000000 := rfl
    have hx : (point 1516+point 1517)/2 = (1447897:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1516
  · change upperValue ((point (1517)+point ((1517)+1))/2) ≤ payment (1517)
    have hp : payment 1517 = (934691012334:ℝ)/1000000000000 := rfl
    have hx : (point 1517+point 1518)/2 = (4345745:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1517
  · change upperValue ((point (1518)+point ((1518)+1))/2) ≤ payment (1518)
    have hp : payment 1518 = (932799828896:ℝ)/1000000000000 := rfl
    have hx : (point 1518+point 1519)/2 = (4347799:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1518
  · change upperValue ((point (1519)+point ((1519)+1))/2) ≤ payment (1519)
    have hp : payment 1519 = (930909426741:ℝ)/1000000000000 := rfl
    have hx : (point 1519+point 1520)/2 = (1449951:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1519
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_094
