import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints029
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_029 (j : Fin 16) : upperValue ((point (16*29+j.val)+point ((16*29+j.val)+1))/2) ≤ payment (16*29+j.val) := by
  fin_cases j
  · change upperValue ((point (464)+point ((464)+1))/2) ≤ payment (464)
    have hp : payment 464 = (4044924423120:ℝ)/1000000000000 := rfl
    have hx : (point 464+point 465)/2 = (2182883:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_464
  · change upperValue ((point (465)+point ((465)+1))/2) ≤ payment (465)
    have hp : payment 465 = (4039672050072:ℝ)/1000000000000 := rfl
    have hx : (point 465+point 466)/2 = (2184937:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_465
  · change upperValue ((point (466)+point ((466)+1))/2) ≤ payment (466)
    have hp : payment 466 = (4034428640005:ℝ)/1000000000000 := rfl
    have hx : (point 466+point 467)/2 = (728997:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_466
  · change upperValue ((point (467)+point ((467)+1))/2) ≤ payment (467)
    have hp : payment 467 = (4029194167068:ℝ)/1000000000000 := rfl
    have hx : (point 467+point 468)/2 = (2189045:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_467
  · change upperValue ((point (468)+point ((468)+1))/2) ≤ payment (468)
    have hp : payment 468 = (4023968605506:ℝ)/1000000000000 := rfl
    have hx : (point 468+point 469)/2 = (2191099:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_468
  · change upperValue ((point (469)+point ((469)+1))/2) ≤ payment (469)
    have hp : payment 469 = (4018751929659:ℝ)/1000000000000 := rfl
    have hx : (point 469+point 470)/2 = (731051:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_469
  · change upperValue ((point (470)+point ((470)+1))/2) ≤ payment (470)
    have hp : payment 470 = (4013544113964:ℝ)/1000000000000 := rfl
    have hx : (point 470+point 471)/2 = (2195207:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_470
  · change upperValue ((point (471)+point ((471)+1))/2) ≤ payment (471)
    have hp : payment 471 = (4008345132952:ℝ)/1000000000000 := rfl
    have hx : (point 471+point 472)/2 = (2197261:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_471
  · change upperValue ((point (472)+point ((472)+1))/2) ≤ payment (472)
    have hp : payment 472 = (4003154961250:ℝ)/1000000000000 := rfl
    have hx : (point 472+point 473)/2 = (733105:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_472
  · change upperValue ((point (473)+point ((473)+1))/2) ≤ payment (473)
    have hp : payment 473 = (3997973573577:ℝ)/1000000000000 := rfl
    have hx : (point 473+point 474)/2 = (2201369:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_473
  · change upperValue ((point (474)+point ((474)+1))/2) ≤ payment (474)
    have hp : payment 474 = (3992800944748:ℝ)/1000000000000 := rfl
    have hx : (point 474+point 475)/2 = (2203423:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_474
  · change upperValue ((point (475)+point ((475)+1))/2) ≤ payment (475)
    have hp : payment 475 = (3987637049669:ℝ)/1000000000000 := rfl
    have hx : (point 475+point 476)/2 = (735159:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_475
  · change upperValue ((point (476)+point ((476)+1))/2) ≤ payment (476)
    have hp : payment 476 = (3982481863341:ℝ)/1000000000000 := rfl
    have hx : (point 476+point 477)/2 = (2207531:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_476
  · change upperValue ((point (477)+point ((477)+1))/2) ≤ payment (477)
    have hp : payment 477 = (3977335360857:ℝ)/1000000000000 := rfl
    have hx : (point 477+point 478)/2 = (2209585:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_477
  · change upperValue ((point (478)+point ((478)+1))/2) ≤ payment (478)
    have hp : payment 478 = (3972197517400:ℝ)/1000000000000 := rfl
    have hx : (point 478+point 479)/2 = (737213:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_478
  · change upperValue ((point (479)+point ((479)+1))/2) ≤ payment (479)
    have hp : payment 479 = (3967068308247:ℝ)/1000000000000 := rfl
    have hx : (point 479+point 480)/2 = (2213693:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_479
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_029
