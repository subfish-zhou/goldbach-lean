import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints030
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_030 (j : Fin 16) : upperValue ((point (16*30+j.val)+point ((16*30+j.val)+1))/2) ≤ payment (16*30+j.val) := by
  fin_cases j
  · change upperValue ((point (480)+point ((480)+1))/2) ≤ payment (480)
    have hp : payment 480 = (3961947708766:ℝ)/1000000000000 := rfl
    have hx : (point 480+point 481)/2 = (2215747:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_480
  · change upperValue ((point (481)+point ((481)+1))/2) ≤ payment (481)
    have hp : payment 481 = (3956835694415:ℝ)/1000000000000 := rfl
    have hx : (point 481+point 482)/2 = (739267:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_481
  · change upperValue ((point (482)+point ((482)+1))/2) ≤ payment (482)
    have hp : payment 482 = (3951732240740:ℝ)/1000000000000 := rfl
    have hx : (point 482+point 483)/2 = (2219855:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_482
  · change upperValue ((point (483)+point ((483)+1))/2) ≤ payment (483)
    have hp : payment 483 = (3946637323382:ℝ)/1000000000000 := rfl
    have hx : (point 483+point 484)/2 = (2221909:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_483
  · change upperValue ((point (484)+point ((484)+1))/2) ≤ payment (484)
    have hp : payment 484 = (3941550918068:ℝ)/1000000000000 := rfl
    have hx : (point 484+point 485)/2 = (741321:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_484
  · change upperValue ((point (485)+point ((485)+1))/2) ≤ payment (485)
    have hp : payment 485 = (3936473000613:ℝ)/1000000000000 := rfl
    have hx : (point 485+point 486)/2 = (2226017:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_485
  · change upperValue ((point (486)+point ((486)+1))/2) ≤ payment (486)
    have hp : payment 486 = (3931403546925:ℝ)/1000000000000 := rfl
    have hx : (point 486+point 487)/2 = (2228071:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_486
  · change upperValue ((point (487)+point ((487)+1))/2) ≤ payment (487)
    have hp : payment 487 = (3926342532996:ℝ)/1000000000000 := rfl
    have hx : (point 487+point 488)/2 = (743375:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_487
  · change upperValue ((point (488)+point ((488)+1))/2) ≤ payment (488)
    have hp : payment 488 = (3921289934908:ℝ)/1000000000000 := rfl
    have hx : (point 488+point 489)/2 = (2232179:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_488
  · change upperValue ((point (489)+point ((489)+1))/2) ≤ payment (489)
    have hp : payment 489 = (3916245728829:ℝ)/1000000000000 := rfl
    have hx : (point 489+point 490)/2 = (2234233:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_489
  · change upperValue ((point (490)+point ((490)+1))/2) ≤ payment (490)
    have hp : payment 490 = (3911209891017:ℝ)/1000000000000 := rfl
    have hx : (point 490+point 491)/2 = (745429:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_490
  · change upperValue ((point (491)+point ((491)+1))/2) ≤ payment (491)
    have hp : payment 491 = (3906182397813:ℝ)/1000000000000 := rfl
    have hx : (point 491+point 492)/2 = (2238341:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_491
  · change upperValue ((point (492)+point ((492)+1))/2) ≤ payment (492)
    have hp : payment 492 = (3901163225646:ℝ)/1000000000000 := rfl
    have hx : (point 492+point 493)/2 = (2240395:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_492
  · change upperValue ((point (493)+point ((493)+1))/2) ≤ payment (493)
    have hp : payment 493 = (3896152351031:ℝ)/1000000000000 := rfl
    have hx : (point 493+point 494)/2 = (747483:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_493
  · change upperValue ((point (494)+point ((494)+1))/2) ≤ payment (494)
    have hp : payment 494 = (3891149750567:ℝ)/1000000000000 := rfl
    have hx : (point 494+point 495)/2 = (2244503:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_494
  · change upperValue ((point (495)+point ((495)+1))/2) ≤ payment (495)
    have hp : payment 495 = (3886155400941:ℝ)/1000000000000 := rfl
    have hx : (point 495+point 496)/2 = (2246557:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_495
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_030
