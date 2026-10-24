import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints049
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_049 (j : Fin 16) : upperValue ((point (16*49+j.val)+point ((16*49+j.val)+1))/2) ≤ payment (16*49+j.val) := by
  fin_cases j
  · change upperValue ((point (784)+point ((784)+1))/2) ≤ payment (784)
    have hp : payment 784 = (2713651852797:ℝ)/1000000000000 := rfl
    have hx : (point 784+point 785)/2 = (946721:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_784
  · change upperValue ((point (785)+point ((785)+1))/2) ≤ payment (785)
    have hp : payment 785 = (2710327063502:ℝ)/1000000000000 := rfl
    have hx : (point 785+point 786)/2 = (2842217:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_785
  · change upperValue ((point (786)+point ((786)+1))/2) ≤ payment (786)
    have hp : payment 786 = (2707006205861:ℝ)/1000000000000 := rfl
    have hx : (point 786+point 787)/2 = (2844271:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_786
  · change upperValue ((point (787)+point ((787)+1))/2) ≤ payment (787)
    have hp : payment 787 = (2703689270732:ℝ)/1000000000000 := rfl
    have hx : (point 787+point 788)/2 = (948775:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_787
  · change upperValue ((point (788)+point ((788)+1))/2) ≤ payment (788)
    have hp : payment 788 = (2700376249000:ℝ)/1000000000000 := rfl
    have hx : (point 788+point 789)/2 = (2848379:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_788
  · change upperValue ((point (789)+point ((789)+1))/2) ≤ payment (789)
    have hp : payment 789 = (2697067131572:ℝ)/1000000000000 := rfl
    have hx : (point 789+point 790)/2 = (2850433:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_789
  · change upperValue ((point (790)+point ((790)+1))/2) ≤ payment (790)
    have hp : payment 790 = (2693761909384:ℝ)/1000000000000 := rfl
    have hx : (point 790+point 791)/2 = (950829:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_790
  · change upperValue ((point (791)+point ((791)+1))/2) ≤ payment (791)
    have hp : payment 791 = (2690460573397:ℝ)/1000000000000 := rfl
    have hx : (point 791+point 792)/2 = (2854541:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_791
  · change upperValue ((point (792)+point ((792)+1))/2) ≤ payment (792)
    have hp : payment 792 = (2687163114595:ℝ)/1000000000000 := rfl
    have hx : (point 792+point 793)/2 = (2856595:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_792
  · change upperValue ((point (793)+point ((793)+1))/2) ≤ payment (793)
    have hp : payment 793 = (2683869523991:ℝ)/1000000000000 := rfl
    have hx : (point 793+point 794)/2 = (952883:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_793
  · change upperValue ((point (794)+point ((794)+1))/2) ≤ payment (794)
    have hp : payment 794 = (2680579792620:ℝ)/1000000000000 := rfl
    have hx : (point 794+point 795)/2 = (2860703:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_794
  · change upperValue ((point (795)+point ((795)+1))/2) ≤ payment (795)
    have hp : payment 795 = (2677293911544:ℝ)/1000000000000 := rfl
    have hx : (point 795+point 796)/2 = (2862757:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_795
  · change upperValue ((point (796)+point ((796)+1))/2) ≤ payment (796)
    have hp : payment 796 = (2674011871850:ℝ)/1000000000000 := rfl
    have hx : (point 796+point 797)/2 = (954937:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_796
  · change upperValue ((point (797)+point ((797)+1))/2) ≤ payment (797)
    have hp : payment 797 = (2670733664649:ℝ)/1000000000000 := rfl
    have hx : (point 797+point 798)/2 = (2866865:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_797
  · change upperValue ((point (798)+point ((798)+1))/2) ≤ payment (798)
    have hp : payment 798 = (2667459281078:ℝ)/1000000000000 := rfl
    have hx : (point 798+point 799)/2 = (2868919:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_798
  · change upperValue ((point (799)+point ((799)+1))/2) ≤ payment (799)
    have hp : payment 799 = (2664188712298:ℝ)/1000000000000 := rfl
    have hx : (point 799+point 800)/2 = (956991:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_799
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_049
