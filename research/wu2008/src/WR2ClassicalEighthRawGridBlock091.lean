import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints091
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_091 (j : Fin 16) : upperValue ((point (16*91+j.val)+point ((16*91+j.val)+1))/2) ≤ payment (16*91+j.val) := by
  fin_cases j
  · change upperValue ((point (1456)+point ((1456)+1))/2) ≤ payment (1456)
    have hp : payment 1456 = (1051609614231:ℝ)/1000000000000 := rfl
    have hx : (point 1456+point 1457)/2 = (1406817:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1456
  · change upperValue ((point (1457)+point ((1457)+1))/2) ≤ payment (1457)
    have hp : payment 1457 = (1049666982023:ℝ)/1000000000000 := rfl
    have hx : (point 1457+point 1458)/2 = (4222505:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1457
  · change upperValue ((point (1458)+point ((1458)+1))/2) ≤ payment (1458)
    have hp : payment 1458 = (1047725255230:ℝ)/1000000000000 := rfl
    have hx : (point 1458+point 1459)/2 = (4224559:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1458
  · change upperValue ((point (1459)+point ((1459)+1))/2) ≤ payment (1459)
    have hp : payment 1459 = (1045784431722:ℝ)/1000000000000 := rfl
    have hx : (point 1459+point 1460)/2 = (1408871:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1459
  · change upperValue ((point (1460)+point ((1460)+1))/2) ≤ payment (1460)
    have hp : payment 1460 = (1043844509376:ℝ)/1000000000000 := rfl
    have hx : (point 1460+point 1461)/2 = (4228667:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1460
  · change upperValue ((point (1461)+point ((1461)+1))/2) ≤ payment (1461)
    have hp : payment 1461 = (1041905486067:ℝ)/1000000000000 := rfl
    have hx : (point 1461+point 1462)/2 = (4230721:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1461
  · change upperValue ((point (1462)+point ((1462)+1))/2) ≤ payment (1462)
    have hp : payment 1462 = (1039967359678:ℝ)/1000000000000 := rfl
    have hx : (point 1462+point 1463)/2 = (1410925:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1462
  · change upperValue ((point (1463)+point ((1463)+1))/2) ≤ payment (1463)
    have hp : payment 1463 = (1038030128093:ℝ)/1000000000000 := rfl
    have hx : (point 1463+point 1464)/2 = (4234829:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1463
  · change upperValue ((point (1464)+point ((1464)+1))/2) ≤ payment (1464)
    have hp : payment 1464 = (1036093789198:ℝ)/1000000000000 := rfl
    have hx : (point 1464+point 1465)/2 = (4236883:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1464
  · change upperValue ((point (1465)+point ((1465)+1))/2) ≤ payment (1465)
    have hp : payment 1465 = (1034158340886:ℝ)/1000000000000 := rfl
    have hx : (point 1465+point 1466)/2 = (1412979:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1465
  · change upperValue ((point (1466)+point ((1466)+1))/2) ≤ payment (1466)
    have hp : payment 1466 = (1032223781050:ℝ)/1000000000000 := rfl
    have hx : (point 1466+point 1467)/2 = (4240991:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1466
  · change upperValue ((point (1467)+point ((1467)+1))/2) ≤ payment (1467)
    have hp : payment 1467 = (1030290107588:ℝ)/1000000000000 := rfl
    have hx : (point 1467+point 1468)/2 = (4243045:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1467
  · change upperValue ((point (1468)+point ((1468)+1))/2) ≤ payment (1468)
    have hp : payment 1468 = (1028357318399:ℝ)/1000000000000 := rfl
    have hx : (point 1468+point 1469)/2 = (1415033:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1468
  · change upperValue ((point (1469)+point ((1469)+1))/2) ≤ payment (1469)
    have hp : payment 1469 = (1026425411389:ℝ)/1000000000000 := rfl
    have hx : (point 1469+point 1470)/2 = (4247153:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1469
  · change upperValue ((point (1470)+point ((1470)+1))/2) ≤ payment (1470)
    have hp : payment 1470 = (1024494384463:ℝ)/1000000000000 := rfl
    have hx : (point 1470+point 1471)/2 = (4249207:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1470
  · change upperValue ((point (1471)+point ((1471)+1))/2) ≤ payment (1471)
    have hp : payment 1471 = (1022564235532:ℝ)/1000000000000 := rfl
    have hx : (point 1471+point 1472)/2 = (1417087:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1471
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_091
