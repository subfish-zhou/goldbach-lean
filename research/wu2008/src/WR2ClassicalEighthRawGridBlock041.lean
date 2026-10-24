import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints041
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_041 (j : Fin 16) : upperValue ((point (16*41+j.val)+point ((16*41+j.val)+1))/2) ≤ payment (16*41+j.val) := by
  fin_cases j
  · change upperValue ((point (656)+point ((656)+1))/2) ≤ payment (656)
    have hp : payment 656 = (3175289767383:ℝ)/1000000000000 := rfl
    have hx : (point 656+point 657)/2 = (2577251:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_656
  · change upperValue ((point (657)+point ((657)+1))/2) ≤ payment (657)
    have hp : payment 657 = (3171375777376:ℝ)/1000000000000 := rfl
    have hx : (point 657+point 658)/2 = (2579305:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_657
  · change upperValue ((point (658)+point ((658)+1))/2) ≤ payment (658)
    have hp : payment 658 = (3167467141240:ℝ)/1000000000000 := rfl
    have hx : (point 658+point 659)/2 = (860453:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_658
  · change upperValue ((point (659)+point ((659)+1))/2) ≤ payment (659)
    have hp : payment 659 = (3163563845582:ℝ)/1000000000000 := rfl
    have hx : (point 659+point 660)/2 = (2583413:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_659
  · change upperValue ((point (660)+point ((660)+1))/2) ≤ payment (660)
    have hp : payment 660 = (3159665877056:ℝ)/1000000000000 := rfl
    have hx : (point 660+point 661)/2 = (2585467:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_660
  · change upperValue ((point (661)+point ((661)+1))/2) ≤ payment (661)
    have hp : payment 661 = (3155773222353:ℝ)/1000000000000 := rfl
    have hx : (point 661+point 662)/2 = (862507:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_661
  · change upperValue ((point (662)+point ((662)+1))/2) ≤ payment (662)
    have hp : payment 662 = (3151885868208:ℝ)/1000000000000 := rfl
    have hx : (point 662+point 663)/2 = (2589575:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_662
  · change upperValue ((point (663)+point ((663)+1))/2) ≤ payment (663)
    have hp : payment 663 = (3148003801398:ℝ)/1000000000000 := rfl
    have hx : (point 663+point 664)/2 = (2591629:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_663
  · change upperValue ((point (664)+point ((664)+1))/2) ≤ payment (664)
    have hp : payment 664 = (3144127008740:ℝ)/1000000000000 := rfl
    have hx : (point 664+point 665)/2 = (864561:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_664
  · change upperValue ((point (665)+point ((665)+1))/2) ≤ payment (665)
    have hp : payment 665 = (3140255477092:ℝ)/1000000000000 := rfl
    have hx : (point 665+point 666)/2 = (2595737:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_665
  · change upperValue ((point (666)+point ((666)+1))/2) ≤ payment (666)
    have hp : payment 666 = (3136389193356:ℝ)/1000000000000 := rfl
    have hx : (point 666+point 667)/2 = (2597791:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_666
  · change upperValue ((point (667)+point ((667)+1))/2) ≤ payment (667)
    have hp : payment 667 = (3132528144471:ℝ)/1000000000000 := rfl
    have hx : (point 667+point 668)/2 = (866615:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_667
  · change upperValue ((point (668)+point ((668)+1))/2) ≤ payment (668)
    have hp : payment 668 = (3128672317418:ℝ)/1000000000000 := rfl
    have hx : (point 668+point 669)/2 = (2601899:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_668
  · change upperValue ((point (669)+point ((669)+1))/2) ≤ payment (669)
    have hp : payment 669 = (3124821699220:ℝ)/1000000000000 := rfl
    have hx : (point 669+point 670)/2 = (2603953:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_669
  · change upperValue ((point (670)+point ((670)+1))/2) ≤ payment (670)
    have hp : payment 670 = (3120976276939:ℝ)/1000000000000 := rfl
    have hx : (point 670+point 671)/2 = (868669:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_670
  · change upperValue ((point (671)+point ((671)+1))/2) ≤ payment (671)
    have hp : payment 671 = (3117136037678:ℝ)/1000000000000 := rfl
    have hx : (point 671+point 672)/2 = (2608061:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_671
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_041
