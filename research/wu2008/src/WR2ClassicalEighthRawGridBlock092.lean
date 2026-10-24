import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints092
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_092 (j : Fin 16) : upperValue ((point (16*92+j.val)+point ((16*92+j.val)+1))/2) ≤ payment (16*92+j.val) := by
  fin_cases j
  · change upperValue ((point (1472)+point ((1472)+1))/2) ≤ payment (1472)
    have hp : payment 1472 = (1020634962510:ℝ)/1000000000000 := rfl
    have hx : (point 1472+point 1473)/2 = (4253315:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1472
  · change upperValue ((point (1473)+point ((1473)+1))/2) ≤ payment (1473)
    have hp : payment 1473 = (1018706563312:ℝ)/1000000000000 := rfl
    have hx : (point 1473+point 1474)/2 = (4255369:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1473
  · change upperValue ((point (1474)+point ((1474)+1))/2) ≤ payment (1474)
    have hp : payment 1474 = (1016779035860:ℝ)/1000000000000 := rfl
    have hx : (point 1474+point 1475)/2 = (1419141:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1474
  · change upperValue ((point (1475)+point ((1475)+1))/2) ≤ payment (1475)
    have hp : payment 1475 = (1014852378075:ℝ)/1000000000000 := rfl
    have hx : (point 1475+point 1476)/2 = (4259477:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1475
  · change upperValue ((point (1476)+point ((1476)+1))/2) ≤ payment (1476)
    have hp : payment 1476 = (1012926587883:ℝ)/1000000000000 := rfl
    have hx : (point 1476+point 1477)/2 = (4261531:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1476
  · change upperValue ((point (1477)+point ((1477)+1))/2) ≤ payment (1477)
    have hp : payment 1477 = (1011001663215:ℝ)/1000000000000 := rfl
    have hx : (point 1477+point 1478)/2 = (1421195:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1477
  · change upperValue ((point (1478)+point ((1478)+1))/2) ≤ payment (1478)
    have hp : payment 1478 = (1009077602002:ℝ)/1000000000000 := rfl
    have hx : (point 1478+point 1479)/2 = (4265639:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1478
  · change upperValue ((point (1479)+point ((1479)+1))/2) ≤ payment (1479)
    have hp : payment 1479 = (1007154402180:ℝ)/1000000000000 := rfl
    have hx : (point 1479+point 1480)/2 = (4267693:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1479
  · change upperValue ((point (1480)+point ((1480)+1))/2) ≤ payment (1480)
    have hp : payment 1480 = (1005232061687:ℝ)/1000000000000 := rfl
    have hx : (point 1480+point 1481)/2 = (1423249:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1480
  · change upperValue ((point (1481)+point ((1481)+1))/2) ≤ payment (1481)
    have hp : payment 1481 = (1003310578466:ℝ)/1000000000000 := rfl
    have hx : (point 1481+point 1482)/2 = (4271801:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1481
  · change upperValue ((point (1482)+point ((1482)+1))/2) ≤ payment (1482)
    have hp : payment 1482 = (1001389950460:ℝ)/1000000000000 := rfl
    have hx : (point 1482+point 1483)/2 = (4273855:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1482
  · change upperValue ((point (1483)+point ((1483)+1))/2) ≤ payment (1483)
    have hp : payment 1483 = (999470175618:ℝ)/1000000000000 := rfl
    have hx : (point 1483+point 1484)/2 = (1425303:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1483
  · change upperValue ((point (1484)+point ((1484)+1))/2) ≤ payment (1484)
    have hp : payment 1484 = (997551251892:ℝ)/1000000000000 := rfl
    have hx : (point 1484+point 1485)/2 = (4277963:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1484
  · change upperValue ((point (1485)+point ((1485)+1))/2) ≤ payment (1485)
    have hp : payment 1485 = (995633177234:ℝ)/1000000000000 := rfl
    have hx : (point 1485+point 1486)/2 = (4280017:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1485
  · change upperValue ((point (1486)+point ((1486)+1))/2) ≤ payment (1486)
    have hp : payment 1486 = (993715949603:ℝ)/1000000000000 := rfl
    have hx : (point 1486+point 1487)/2 = (1427357:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1486
  · change upperValue ((point (1487)+point ((1487)+1))/2) ≤ payment (1487)
    have hp : payment 1487 = (991799566959:ℝ)/1000000000000 := rfl
    have hx : (point 1487+point 1488)/2 = (4284125:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1487
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_092
