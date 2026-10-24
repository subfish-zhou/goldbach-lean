import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints037
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_037 (j : Fin 16) : upperValue ((point (16*37+j.val)+point ((16*37+j.val)+1))/2) ≤ payment (16*37+j.val) := by
  fin_cases j
  · change upperValue ((point (592)+point ((592)+1))/2) ≤ payment (592)
    have hp : payment 592 = (3437567987411:ℝ)/1000000000000 := rfl
    have hx : (point 592+point 593)/2 = (815265:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_592
  · change upperValue ((point (593)+point ((593)+1))/2) ≤ payment (593)
    have hp : payment 593 = (3433281437268:ℝ)/1000000000000 := rfl
    have hx : (point 593+point 594)/2 = (2447849:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_593
  · change upperValue ((point (594)+point ((594)+1))/2) ≤ payment (594)
    have hp : payment 594 = (3429001193707:ℝ)/1000000000000 := rfl
    have hx : (point 594+point 595)/2 = (2449903:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_594
  · change upperValue ((point (595)+point ((595)+1))/2) ≤ payment (595)
    have hp : payment 595 = (3424727240262:ℝ)/1000000000000 := rfl
    have hx : (point 595+point 596)/2 = (817319:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_595
  · change upperValue ((point (596)+point ((596)+1))/2) ≤ payment (596)
    have hp : payment 596 = (3420459560518:ℝ)/1000000000000 := rfl
    have hx : (point 596+point 597)/2 = (2454011:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_596
  · change upperValue ((point (597)+point ((597)+1))/2) ≤ payment (597)
    have hp : payment 597 = (3416198138117:ℝ)/1000000000000 := rfl
    have hx : (point 597+point 598)/2 = (2456065:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_597
  · change upperValue ((point (598)+point ((598)+1))/2) ≤ payment (598)
    have hp : payment 598 = (3411942956754:ℝ)/1000000000000 := rfl
    have hx : (point 598+point 599)/2 = (819373:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_598
  · change upperValue ((point (599)+point ((599)+1))/2) ≤ payment (599)
    have hp : payment 599 = (3407694000179:ℝ)/1000000000000 := rfl
    have hx : (point 599+point 600)/2 = (2460173:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_599
  · change upperValue ((point (600)+point ((600)+1))/2) ≤ payment (600)
    have hp : payment 600 = (3403451252195:ℝ)/1000000000000 := rfl
    have hx : (point 600+point 601)/2 = (2462227:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_600
  · change upperValue ((point (601)+point ((601)+1))/2) ≤ payment (601)
    have hp : payment 601 = (3399214696658:ℝ)/1000000000000 := rfl
    have hx : (point 601+point 602)/2 = (821427:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_601
  · change upperValue ((point (602)+point ((602)+1))/2) ≤ payment (602)
    have hp : payment 602 = (3394984317478:ℝ)/1000000000000 := rfl
    have hx : (point 602+point 603)/2 = (2466335:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_602
  · change upperValue ((point (603)+point ((603)+1))/2) ≤ payment (603)
    have hp : payment 603 = (3390760098618:ℝ)/1000000000000 := rfl
    have hx : (point 603+point 604)/2 = (2468389:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_603
  · change upperValue ((point (604)+point ((604)+1))/2) ≤ payment (604)
    have hp : payment 604 = (3386542024093:ℝ)/1000000000000 := rfl
    have hx : (point 604+point 605)/2 = (823481:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_604
  · change upperValue ((point (605)+point ((605)+1))/2) ≤ payment (605)
    have hp : payment 605 = (3382330077971:ℝ)/1000000000000 := rfl
    have hx : (point 605+point 606)/2 = (2472497:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_605
  · change upperValue ((point (606)+point ((606)+1))/2) ≤ payment (606)
    have hp : payment 606 = (3378124244374:ℝ)/1000000000000 := rfl
    have hx : (point 606+point 607)/2 = (2474551:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_606
  · change upperValue ((point (607)+point ((607)+1))/2) ≤ payment (607)
    have hp : payment 607 = (3373924507473:ℝ)/1000000000000 := rfl
    have hx : (point 607+point 608)/2 = (825535:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_607
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_037
