import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints035
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_035 (j : Fin 16) : upperValue ((point (16*35+j.val)+point ((16*35+j.val)+1))/2) ≤ payment (16*35+j.val) := by
  fin_cases j
  · change upperValue ((point (560)+point ((560)+1))/2) ≤ payment (560)
    have hp : payment 560 = (3578168958215:ℝ)/1000000000000 := rfl
    have hx : (point 560+point 561)/2 = (2380067:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_560
  · change upperValue ((point (561)+point ((561)+1))/2) ≤ payment (561)
    have hp : payment 561 = (3573671563321:ℝ)/1000000000000 := rfl
    have hx : (point 561+point 562)/2 = (2382121:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_561
  · change upperValue ((point (562)+point ((562)+1))/2) ≤ payment (562)
    have hp : payment 562 = (3569181032238:ℝ)/1000000000000 := rfl
    have hx : (point 562+point 563)/2 = (794725:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_562
  · change upperValue ((point (563)+point ((563)+1))/2) ≤ payment (563)
    have hp : payment 563 = (3564697346623:ℝ)/1000000000000 := rfl
    have hx : (point 563+point 564)/2 = (2386229:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_563
  · change upperValue ((point (564)+point ((564)+1))/2) ≤ payment (564)
    have hp : payment 564 = (3560220488194:ℝ)/1000000000000 := rfl
    have hx : (point 564+point 565)/2 = (2388283:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_564
  · change upperValue ((point (565)+point ((565)+1))/2) ≤ payment (565)
    have hp : payment 565 = (3555750438735:ℝ)/1000000000000 := rfl
    have hx : (point 565+point 566)/2 = (796779:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_565
  · change upperValue ((point (566)+point ((566)+1))/2) ≤ payment (566)
    have hp : payment 566 = (3551287180088:ℝ)/1000000000000 := rfl
    have hx : (point 566+point 567)/2 = (2392391:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_566
  · change upperValue ((point (567)+point ((567)+1))/2) ≤ payment (567)
    have hp : payment 567 = (3546830694160:ℝ)/1000000000000 := rfl
    have hx : (point 567+point 568)/2 = (2394445:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_567
  · change upperValue ((point (568)+point ((568)+1))/2) ≤ payment (568)
    have hp : payment 568 = (3542380962917:ℝ)/1000000000000 := rfl
    have hx : (point 568+point 569)/2 = (798833:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_568
  · change upperValue ((point (569)+point ((569)+1))/2) ≤ payment (569)
    have hp : payment 569 = (3537937968389:ℝ)/1000000000000 := rfl
    have hx : (point 569+point 570)/2 = (2398553:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_569
  · change upperValue ((point (570)+point ((570)+1))/2) ≤ payment (570)
    have hp : payment 570 = (3533501692664:ℝ)/1000000000000 := rfl
    have hx : (point 570+point 571)/2 = (2400607:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_570
  · change upperValue ((point (571)+point ((571)+1))/2) ≤ payment (571)
    have hp : payment 571 = (3529072117892:ℝ)/1000000000000 := rfl
    have hx : (point 571+point 572)/2 = (800887:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_571
  · change upperValue ((point (572)+point ((572)+1))/2) ≤ payment (572)
    have hp : payment 572 = (3524649226285:ℝ)/1000000000000 := rfl
    have hx : (point 572+point 573)/2 = (2404715:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_572
  · change upperValue ((point (573)+point ((573)+1))/2) ≤ payment (573)
    have hp : payment 573 = (3520233000112:ℝ)/1000000000000 := rfl
    have hx : (point 573+point 574)/2 = (2406769:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_573
  · change upperValue ((point (574)+point ((574)+1))/2) ≤ payment (574)
    have hp : payment 574 = (3515823421706:ℝ)/1000000000000 := rfl
    have hx : (point 574+point 575)/2 = (802941:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_574
  · change upperValue ((point (575)+point ((575)+1))/2) ≤ payment (575)
    have hp : payment 575 = (3511420473455:ℝ)/1000000000000 := rfl
    have hx : (point 575+point 576)/2 = (2410877:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_575
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_035
