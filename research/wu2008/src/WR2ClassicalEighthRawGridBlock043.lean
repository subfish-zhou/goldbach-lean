import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints043
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_043 (j : Fin 16) : upperValue ((point (16*43+j.val)+point ((16*43+j.val)+1))/2) ≤ payment (16*43+j.val) := by
  fin_cases j
  · change upperValue ((point (688)+point ((688)+1))/2) ≤ payment (688)
    have hp : payment 688 = (3052632666113:ℝ)/1000000000000 := rfl
    have hx : (point 688+point 689)/2 = (880993:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_688
  · change upperValue ((point (689)+point ((689)+1))/2) ≤ payment (689)
    have hp : payment 689 = (3048883560629:ℝ)/1000000000000 := rfl
    have hx : (point 689+point 690)/2 = (2645033:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_689
  · change upperValue ((point (690)+point ((690)+1))/2) ≤ payment (690)
    have hp : payment 690 = (3045139400545:ℝ)/1000000000000 := rfl
    have hx : (point 690+point 691)/2 = (2647087:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_690
  · change upperValue ((point (691)+point ((691)+1))/2) ≤ payment (691)
    have hp : payment 691 = (3041400173735:ℝ)/1000000000000 := rfl
    have hx : (point 691+point 692)/2 = (883047:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_691
  · change upperValue ((point (692)+point ((692)+1))/2) ≤ payment (692)
    have hp : payment 692 = (3037665868111:ℝ)/1000000000000 := rfl
    have hx : (point 692+point 693)/2 = (2651195:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_692
  · change upperValue ((point (693)+point ((693)+1))/2) ≤ payment (693)
    have hp : payment 693 = (3033936471622:ℝ)/1000000000000 := rfl
    have hx : (point 693+point 694)/2 = (2653249:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_693
  · change upperValue ((point (694)+point ((694)+1))/2) ≤ payment (694)
    have hp : payment 694 = (3030211972251:ℝ)/1000000000000 := rfl
    have hx : (point 694+point 695)/2 = (885101:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_694
  · change upperValue ((point (695)+point ((695)+1))/2) ≤ payment (695)
    have hp : payment 695 = (3026492358022:ℝ)/1000000000000 := rfl
    have hx : (point 695+point 696)/2 = (2657357:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_695
  · change upperValue ((point (696)+point ((696)+1))/2) ≤ payment (696)
    have hp : payment 696 = (3022777616991:ℝ)/1000000000000 := rfl
    have hx : (point 696+point 697)/2 = (2659411:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_696
  · change upperValue ((point (697)+point ((697)+1))/2) ≤ payment (697)
    have hp : payment 697 = (3019067737254:ℝ)/1000000000000 := rfl
    have hx : (point 697+point 698)/2 = (887155:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_697
  · change upperValue ((point (698)+point ((698)+1))/2) ≤ payment (698)
    have hp : payment 698 = (3015362706940:ℝ)/1000000000000 := rfl
    have hx : (point 698+point 699)/2 = (2663519:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_698
  · change upperValue ((point (699)+point ((699)+1))/2) ≤ payment (699)
    have hp : payment 699 = (3011662514217:ℝ)/1000000000000 := rfl
    have hx : (point 699+point 700)/2 = (2665573:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_699
  · change upperValue ((point (700)+point ((700)+1))/2) ≤ payment (700)
    have hp : payment 700 = (3007967147287:ℝ)/1000000000000 := rfl
    have hx : (point 700+point 701)/2 = (889209:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_700
  · change upperValue ((point (701)+point ((701)+1))/2) ≤ payment (701)
    have hp : payment 701 = (3004276594389:ℝ)/1000000000000 := rfl
    have hx : (point 701+point 702)/2 = (2669681:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_701
  · change upperValue ((point (702)+point ((702)+1))/2) ≤ payment (702)
    have hp : payment 702 = (3000590843796:ℝ)/1000000000000 := rfl
    have hx : (point 702+point 703)/2 = (2671735:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_702
  · change upperValue ((point (703)+point ((703)+1))/2) ≤ payment (703)
    have hp : payment 703 = (2996909883818:ℝ)/1000000000000 := rfl
    have hx : (point 703+point 704)/2 = (891263:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_703
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_043
