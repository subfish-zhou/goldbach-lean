import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints036
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_036 (j : Fin 16) : upperValue ((point (16*36+j.val)+point ((16*36+j.val)+1))/2) ≤ payment (16*36+j.val) := by
  fin_cases j
  · change upperValue ((point (576)+point ((576)+1))/2) ≤ payment (576)
    have hp : payment 576 = (3507024137810:ℝ)/1000000000000 := rfl
    have hx : (point 576+point 577)/2 = (2412931:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_576
  · change upperValue ((point (577)+point ((577)+1))/2) ≤ payment (577)
    have hp : payment 577 = (3502634397280:ℝ)/1000000000000 := rfl
    have hx : (point 577+point 578)/2 = (804995:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_577
  · change upperValue ((point (578)+point ((578)+1))/2) ≤ payment (578)
    have hp : payment 578 = (3498251234432:ℝ)/1000000000000 := rfl
    have hx : (point 578+point 579)/2 = (2417039:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_578
  · change upperValue ((point (579)+point ((579)+1))/2) ≤ payment (579)
    have hp : payment 579 = (3493874631894:ℝ)/1000000000000 := rfl
    have hx : (point 579+point 580)/2 = (2419093:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_579
  · change upperValue ((point (580)+point ((580)+1))/2) ≤ payment (580)
    have hp : payment 580 = (3489504572351:ℝ)/1000000000000 := rfl
    have hx : (point 580+point 581)/2 = (807049:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_580
  · change upperValue ((point (581)+point ((581)+1))/2) ≤ payment (581)
    have hp : payment 581 = (3485141038545:ℝ)/1000000000000 := rfl
    have hx : (point 581+point 582)/2 = (2423201:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_581
  · change upperValue ((point (582)+point ((582)+1))/2) ≤ payment (582)
    have hp : payment 582 = (3480784013277:ℝ)/1000000000000 := rfl
    have hx : (point 582+point 583)/2 = (2425255:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_582
  · change upperValue ((point (583)+point ((583)+1))/2) ≤ payment (583)
    have hp : payment 583 = (3476433479408:ℝ)/1000000000000 := rfl
    have hx : (point 583+point 584)/2 = (809103:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_583
  · change upperValue ((point (584)+point ((584)+1))/2) ≤ payment (584)
    have hp : payment 584 = (3472089419851:ℝ)/1000000000000 := rfl
    have hx : (point 584+point 585)/2 = (2429363:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_584
  · change upperValue ((point (585)+point ((585)+1))/2) ≤ payment (585)
    have hp : payment 585 = (3467751817583:ℝ)/1000000000000 := rfl
    have hx : (point 585+point 586)/2 = (2431417:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_585
  · change upperValue ((point (586)+point ((586)+1))/2) ≤ payment (586)
    have hp : payment 586 = (3463420655631:ℝ)/1000000000000 := rfl
    have hx : (point 586+point 587)/2 = (811157:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_586
  · change upperValue ((point (587)+point ((587)+1))/2) ≤ payment (587)
    have hp : payment 587 = (3459095917085:ℝ)/1000000000000 := rfl
    have hx : (point 587+point 588)/2 = (2435525:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_587
  · change upperValue ((point (588)+point ((588)+1))/2) ≤ payment (588)
    have hp : payment 588 = (3454777585086:ℝ)/1000000000000 := rfl
    have hx : (point 588+point 589)/2 = (2437579:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_588
  · change upperValue ((point (589)+point ((589)+1))/2) ≤ payment (589)
    have hp : payment 589 = (3450465642836:ℝ)/1000000000000 := rfl
    have hx : (point 589+point 590)/2 = (813211:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_589
  · change upperValue ((point (590)+point ((590)+1))/2) ≤ payment (590)
    have hp : payment 590 = (3446160073590:ℝ)/1000000000000 := rfl
    have hx : (point 590+point 591)/2 = (2441687:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_590
  · change upperValue ((point (591)+point ((591)+1))/2) ≤ payment (591)
    have hp : payment 591 = (3441860860659:ℝ)/1000000000000 := rfl
    have hx : (point 591+point 592)/2 = (2443741:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_591
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_036
