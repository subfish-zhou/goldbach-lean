import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints033
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_033 (j : Fin 16) : upperValue ((point (16*33+j.val)+point ((16*33+j.val)+1))/2) ≤ payment (16*33+j.val) := by
  fin_cases j
  · change upperValue ((point (528)+point ((528)+1))/2) ≤ payment (528)
    have hp : payment 528 = (3725822832468:ℝ)/1000000000000 := rfl
    have hx : (point 528+point 529)/2 = (2314339:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_528
  · change upperValue ((point (529)+point ((529)+1))/2) ≤ payment (529)
    have hp : payment 529 = (3721095721449:ℝ)/1000000000000 := rfl
    have hx : (point 529+point 530)/2 = (772131:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_529
  · change upperValue ((point (530)+point ((530)+1))/2) ≤ payment (530)
    have hp : payment 530 = (3716376095944:ℝ)/1000000000000 := rfl
    have hx : (point 530+point 531)/2 = (2318447:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_530
  · change upperValue ((point (531)+point ((531)+1))/2) ≤ payment (531)
    have hp : payment 531 = (3711663935455:ℝ)/1000000000000 := rfl
    have hx : (point 531+point 532)/2 = (2320501:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_531
  · change upperValue ((point (532)+point ((532)+1))/2) ≤ payment (532)
    have hp : payment 532 = (3706959219559:ℝ)/1000000000000 := rfl
    have hx : (point 532+point 533)/2 = (774185:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_532
  · change upperValue ((point (533)+point ((533)+1))/2) ≤ payment (533)
    have hp : payment 533 = (3702261927902:ℝ)/1000000000000 := rfl
    have hx : (point 533+point 534)/2 = (2324609:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_533
  · change upperValue ((point (534)+point ((534)+1))/2) ≤ payment (534)
    have hp : payment 534 = (3697572040203:ℝ)/1000000000000 := rfl
    have hx : (point 534+point 535)/2 = (2326663:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_534
  · change upperValue ((point (535)+point ((535)+1))/2) ≤ payment (535)
    have hp : payment 535 = (3692889536252:ℝ)/1000000000000 := rfl
    have hx : (point 535+point 536)/2 = (776239:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_535
  · change upperValue ((point (536)+point ((536)+1))/2) ≤ payment (536)
    have hp : payment 536 = (3688214395910:ℝ)/1000000000000 := rfl
    have hx : (point 536+point 537)/2 = (2330771:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_536
  · change upperValue ((point (537)+point ((537)+1))/2) ≤ payment (537)
    have hp : payment 537 = (3683546599107:ℝ)/1000000000000 := rfl
    have hx : (point 537+point 538)/2 = (2332825:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_537
  · change upperValue ((point (538)+point ((538)+1))/2) ≤ payment (538)
    have hp : payment 538 = (3678886125843:ℝ)/1000000000000 := rfl
    have hx : (point 538+point 539)/2 = (778293:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_538
  · change upperValue ((point (539)+point ((539)+1))/2) ≤ payment (539)
    have hp : payment 539 = (3674232956191:ℝ)/1000000000000 := rfl
    have hx : (point 539+point 540)/2 = (2336933:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_539
  · change upperValue ((point (540)+point ((540)+1))/2) ≤ payment (540)
    have hp : payment 540 = (3669587070289:ℝ)/1000000000000 := rfl
    have hx : (point 540+point 541)/2 = (2338987:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_540
  · change upperValue ((point (541)+point ((541)+1))/2) ≤ payment (541)
    have hp : payment 541 = (3664948448348:ℝ)/1000000000000 := rfl
    have hx : (point 541+point 542)/2 = (780347:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_541
  · change upperValue ((point (542)+point ((542)+1))/2) ≤ payment (542)
    have hp : payment 542 = (3660317070645:ℝ)/1000000000000 := rfl
    have hx : (point 542+point 543)/2 = (2343095:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_542
  · change upperValue ((point (543)+point ((543)+1))/2) ≤ payment (543)
    have hp : payment 543 = (3655692917526:ℝ)/1000000000000 := rfl
    have hx : (point 543+point 544)/2 = (2345149:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_543
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_033
