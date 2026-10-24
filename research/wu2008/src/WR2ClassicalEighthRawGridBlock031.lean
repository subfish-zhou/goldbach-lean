import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints031
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_031 (j : Fin 16) : upperValue ((point (16*31+j.val)+point ((16*31+j.val)+1))/2) ≤ payment (16*31+j.val) := by
  fin_cases j
  · change upperValue ((point (496)+point ((496)+1))/2) ≤ payment (496)
    have hp : payment 496 = (3881169278922:ℝ)/1000000000000 := rfl
    have hx : (point 496+point 497)/2 = (749537:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_496
  · change upperValue ((point (497)+point ((497)+1))/2) ≤ payment (497)
    have hp : payment 497 = (3876191361364:ℝ)/1000000000000 := rfl
    have hx : (point 497+point 498)/2 = (2250665:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_497
  · change upperValue ((point (498)+point ((498)+1))/2) ≤ payment (498)
    have hp : payment 498 = (3871221625205:ℝ)/1000000000000 := rfl
    have hx : (point 498+point 499)/2 = (2252719:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_498
  · change upperValue ((point (499)+point ((499)+1))/2) ≤ payment (499)
    have hp : payment 499 = (3866260047466:ℝ)/1000000000000 := rfl
    have hx : (point 499+point 500)/2 = (751591:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_499
  · change upperValue ((point (500)+point ((500)+1))/2) ≤ payment (500)
    have hp : payment 500 = (3861306605252:ℝ)/1000000000000 := rfl
    have hx : (point 500+point 501)/2 = (2256827:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_500
  · change upperValue ((point (501)+point ((501)+1))/2) ≤ payment (501)
    have hp : payment 501 = (3856361275751:ℝ)/1000000000000 := rfl
    have hx : (point 501+point 502)/2 = (2258881:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_501
  · change upperValue ((point (502)+point ((502)+1))/2) ≤ payment (502)
    have hp : payment 502 = (3851424036232:ℝ)/1000000000000 := rfl
    have hx : (point 502+point 503)/2 = (753645:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_502
  · change upperValue ((point (503)+point ((503)+1))/2) ≤ payment (503)
    have hp : payment 503 = (3846494864046:ℝ)/1000000000000 := rfl
    have hx : (point 503+point 504)/2 = (2262989:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_503
  · change upperValue ((point (504)+point ((504)+1))/2) ≤ payment (504)
    have hp : payment 504 = (3841573736629:ℝ)/1000000000000 := rfl
    have hx : (point 504+point 505)/2 = (2265043:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_504
  · change upperValue ((point (505)+point ((505)+1))/2) ≤ payment (505)
    have hp : payment 505 = (3836660631493:ℝ)/1000000000000 := rfl
    have hx : (point 505+point 506)/2 = (755699:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_505
  · change upperValue ((point (506)+point ((506)+1))/2) ≤ payment (506)
    have hp : payment 506 = (3831755526234:ℝ)/1000000000000 := rfl
    have hx : (point 506+point 507)/2 = (2269151:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_506
  · change upperValue ((point (507)+point ((507)+1))/2) ≤ payment (507)
    have hp : payment 507 = (3826858398529:ℝ)/1000000000000 := rfl
    have hx : (point 507+point 508)/2 = (2271205:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_507
  · change upperValue ((point (508)+point ((508)+1))/2) ≤ payment (508)
    have hp : payment 508 = (3821969226134:ℝ)/1000000000000 := rfl
    have hx : (point 508+point 509)/2 = (757753:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_508
  · change upperValue ((point (509)+point ((509)+1))/2) ≤ payment (509)
    have hp : payment 509 = (3817087986884:ℝ)/1000000000000 := rfl
    have hx : (point 509+point 510)/2 = (2275313:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_509
  · change upperValue ((point (510)+point ((510)+1))/2) ≤ payment (510)
    have hp : payment 510 = (3812214658696:ℝ)/1000000000000 := rfl
    have hx : (point 510+point 511)/2 = (2277367:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_510
  · change upperValue ((point (511)+point ((511)+1))/2) ≤ payment (511)
    have hp : payment 511 = (3807349219563:ℝ)/1000000000000 := rfl
    have hx : (point 511+point 512)/2 = (759807:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_511
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_031
