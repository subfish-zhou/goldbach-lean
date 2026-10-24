import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints006
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_006 (j : Fin 16) : upperValue ((point (16*6+j.val)+point ((16*6+j.val)+1))/2) ≤ payment (16*6+j.val) := by
  fin_cases j
  · change upperValue ((point (96)+point ((96)+1))/2) ≤ payment (96)
    have hp : payment 96 = (6917845540361:ℝ)/1000000000000 := rfl
    have hx : (point 96+point 97)/2 = (1427011:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_96
  · change upperValue ((point (97)+point ((97)+1))/2) ≤ payment (97)
    have hp : payment 97 = (6906135814063:ℝ)/1000000000000 := rfl
    have hx : (point 97+point 98)/2 = (476355:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_97
  · change upperValue ((point (98)+point ((98)+1))/2) ≤ payment (98)
    have hp : payment 98 = (6894458622002:ℝ)/1000000000000 := rfl
    have hx : (point 98+point 99)/2 = (1431119:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_98
  · change upperValue ((point (99)+point ((99)+1))/2) ≤ payment (99)
    have hp : payment 99 = (6882813823594:ℝ)/1000000000000 := rfl
    have hx : (point 99+point 100)/2 = (1433173:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_99
  · change upperValue ((point (100)+point ((100)+1))/2) ≤ payment (100)
    have hp : payment 100 = (6871201279056:ℝ)/1000000000000 := rfl
    have hx : (point 100+point 101)/2 = (478409:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_100
  · change upperValue ((point (101)+point ((101)+1))/2) ≤ payment (101)
    have hp : payment 101 = (6859620849407:ℝ)/1000000000000 := rfl
    have hx : (point 101+point 102)/2 = (1437281:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_101
  · change upperValue ((point (102)+point ((102)+1))/2) ≤ payment (102)
    have hp : payment 102 = (6848072396455:ℝ)/1000000000000 := rfl
    have hx : (point 102+point 103)/2 = (1439335:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_102
  · change upperValue ((point (103)+point ((103)+1))/2) ≤ payment (103)
    have hp : payment 103 = (6836555782798:ℝ)/1000000000000 := rfl
    have hx : (point 103+point 104)/2 = (480463:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_103
  · change upperValue ((point (104)+point ((104)+1))/2) ≤ payment (104)
    have hp : payment 104 = (6825070871814:ℝ)/1000000000000 := rfl
    have hx : (point 104+point 105)/2 = (1443443:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_104
  · change upperValue ((point (105)+point ((105)+1))/2) ≤ payment (105)
    have hp : payment 105 = (6813617527657:ℝ)/1000000000000 := rfl
    have hx : (point 105+point 106)/2 = (1445497:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_105
  · change upperValue ((point (106)+point ((106)+1))/2) ≤ payment (106)
    have hp : payment 106 = (6802195615254:ℝ)/1000000000000 := rfl
    have hx : (point 106+point 107)/2 = (482517:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_106
  · change upperValue ((point (107)+point ((107)+1))/2) ≤ payment (107)
    have hp : payment 107 = (6790805000293:ℝ)/1000000000000 := rfl
    have hx : (point 107+point 108)/2 = (1449605:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_107
  · change upperValue ((point (108)+point ((108)+1))/2) ≤ payment (108)
    have hp : payment 108 = (6779445549224:ℝ)/1000000000000 := rfl
    have hx : (point 108+point 109)/2 = (1451659:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_108
  · change upperValue ((point (109)+point ((109)+1))/2) ≤ payment (109)
    have hp : payment 109 = (6768117129252:ℝ)/1000000000000 := rfl
    have hx : (point 109+point 110)/2 = (484571:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_109
  · change upperValue ((point (110)+point ((110)+1))/2) ≤ payment (110)
    have hp : payment 110 = (6756819608328:ℝ)/1000000000000 := rfl
    have hx : (point 110+point 111)/2 = (1455767:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_110
  · change upperValue ((point (111)+point ((111)+1))/2) ≤ payment (111)
    have hp : payment 111 = (6745552855150:ℝ)/1000000000000 := rfl
    have hx : (point 111+point 112)/2 = (1457821:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_111
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_006
