import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints044
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_044 (j : Fin 16) : upperValue ((point (16*44+j.val)+point ((16*44+j.val)+1))/2) ≤ payment (16*44+j.val) := by
  fin_cases j
  · change upperValue ((point (704)+point ((704)+1))/2) ≤ payment (704)
    have hp : payment 704 = (2993233702799:ℝ)/1000000000000 := rfl
    have hx : (point 704+point 705)/2 = (2675843:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_704
  · change upperValue ((point (705)+point ((705)+1))/2) ≤ payment (705)
    have hp : payment 705 = (2989562289119:ℝ)/1000000000000 := rfl
    have hx : (point 705+point 706)/2 = (2677897:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_705
  · change upperValue ((point (706)+point ((706)+1))/2) ≤ payment (706)
    have hp : payment 706 = (2985895631194:ℝ)/1000000000000 := rfl
    have hx : (point 706+point 707)/2 = (893317:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_706
  · change upperValue ((point (707)+point ((707)+1))/2) ≤ payment (707)
    have hp : payment 707 = (2982233717473:ℝ)/1000000000000 := rfl
    have hx : (point 707+point 708)/2 = (2682005:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_707
  · change upperValue ((point (708)+point ((708)+1))/2) ≤ payment (708)
    have hp : payment 708 = (2978576536442:ℝ)/1000000000000 := rfl
    have hx : (point 708+point 709)/2 = (2684059:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_708
  · change upperValue ((point (709)+point ((709)+1))/2) ≤ payment (709)
    have hp : payment 709 = (2974924076619:ℝ)/1000000000000 := rfl
    have hx : (point 709+point 710)/2 = (895371:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_709
  · change upperValue ((point (710)+point ((710)+1))/2) ≤ payment (710)
    have hp : payment 710 = (2971276326559:ℝ)/1000000000000 := rfl
    have hx : (point 710+point 711)/2 = (2688167:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_710
  · change upperValue ((point (711)+point ((711)+1))/2) ≤ payment (711)
    have hp : payment 711 = (2967633274850:ℝ)/1000000000000 := rfl
    have hx : (point 711+point 712)/2 = (2690221:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_711
  · change upperValue ((point (712)+point ((712)+1))/2) ≤ payment (712)
    have hp : payment 712 = (2963994910115:ℝ)/1000000000000 := rfl
    have hx : (point 712+point 713)/2 = (897425:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_712
  · change upperValue ((point (713)+point ((713)+1))/2) ≤ payment (713)
    have hp : payment 713 = (2960361221010:ℝ)/1000000000000 := rfl
    have hx : (point 713+point 714)/2 = (2694329:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_713
  · change upperValue ((point (714)+point ((714)+1))/2) ≤ payment (714)
    have hp : payment 714 = (2956732196227:ℝ)/1000000000000 := rfl
    have hx : (point 714+point 715)/2 = (2696383:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_714
  · change upperValue ((point (715)+point ((715)+1))/2) ≤ payment (715)
    have hp : payment 715 = (2953107824489:ℝ)/1000000000000 := rfl
    have hx : (point 715+point 716)/2 = (899479:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_715
  · change upperValue ((point (716)+point ((716)+1))/2) ≤ payment (716)
    have hp : payment 716 = (2949488094557:ℝ)/1000000000000 := rfl
    have hx : (point 716+point 717)/2 = (2700491:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_716
  · change upperValue ((point (717)+point ((717)+1))/2) ≤ payment (717)
    have hp : payment 717 = (2945872995221:ℝ)/1000000000000 := rfl
    have hx : (point 717+point 718)/2 = (2702545:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_717
  · change upperValue ((point (718)+point ((718)+1))/2) ≤ payment (718)
    have hp : payment 718 = (2942262515307:ℝ)/1000000000000 := rfl
    have hx : (point 718+point 719)/2 = (901533:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_718
  · change upperValue ((point (719)+point ((719)+1))/2) ≤ payment (719)
    have hp : payment 719 = (2938656643675:ℝ)/1000000000000 := rfl
    have hx : (point 719+point 720)/2 = (2706653:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_719
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_044
