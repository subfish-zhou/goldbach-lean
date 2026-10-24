import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints047
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_047 (j : Fin 16) : upperValue ((point (16*47+j.val)+point ((16*47+j.val)+1))/2) ≤ payment (16*47+j.val) := by
  fin_cases j
  · change upperValue ((point (752)+point ((752)+1))/2) ≤ payment (752)
    have hp : payment 752 = (2822177119059:ℝ)/1000000000000 := rfl
    have hx : (point 752+point 753)/2 = (2774435:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_752
  · change upperValue ((point (753)+point ((753)+1))/2) ≤ payment (753)
    have hp : payment 753 = (2818721530182:ℝ)/1000000000000 := rfl
    have hx : (point 753+point 754)/2 = (2776489:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_753
  · change upperValue ((point (754)+point ((754)+1))/2) ≤ payment (754)
    have hp : payment 754 = (2815270179722:ℝ)/1000000000000 := rfl
    have hx : (point 754+point 755)/2 = (926181:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_754
  · change upperValue ((point (755)+point ((755)+1))/2) ≤ payment (755)
    have hp : payment 755 = (2811823057660:ℝ)/1000000000000 := rfl
    have hx : (point 755+point 756)/2 = (2780597:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_755
  · change upperValue ((point (756)+point ((756)+1))/2) ≤ payment (756)
    have hp : payment 756 = (2808380154003:ℝ)/1000000000000 := rfl
    have hx : (point 756+point 757)/2 = (2782651:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_756
  · change upperValue ((point (757)+point ((757)+1))/2) ≤ payment (757)
    have hp : payment 757 = (2804941458790:ℝ)/1000000000000 := rfl
    have hx : (point 757+point 758)/2 = (928235:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_757
  · change upperValue ((point (758)+point ((758)+1))/2) ≤ payment (758)
    have hp : payment 758 = (2801506962088:ℝ)/1000000000000 := rfl
    have hx : (point 758+point 759)/2 = (2786759:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_758
  · change upperValue ((point (759)+point ((759)+1))/2) ≤ payment (759)
    have hp : payment 759 = (2798076653991:ℝ)/1000000000000 := rfl
    have hx : (point 759+point 760)/2 = (2788813:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_759
  · change upperValue ((point (760)+point ((760)+1))/2) ≤ payment (760)
    have hp : payment 760 = (2794650524624:ℝ)/1000000000000 := rfl
    have hx : (point 760+point 761)/2 = (930289:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_760
  · change upperValue ((point (761)+point ((761)+1))/2) ≤ payment (761)
    have hp : payment 761 = (2791228564139:ℝ)/1000000000000 := rfl
    have hx : (point 761+point 762)/2 = (2792921:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_761
  · change upperValue ((point (762)+point ((762)+1))/2) ≤ payment (762)
    have hp : payment 762 = (2787810762718:ℝ)/1000000000000 := rfl
    have hx : (point 762+point 763)/2 = (2794975:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_762
  · change upperValue ((point (763)+point ((763)+1))/2) ≤ payment (763)
    have hp : payment 763 = (2784397110568:ℝ)/1000000000000 := rfl
    have hx : (point 763+point 764)/2 = (932343:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_763
  · change upperValue ((point (764)+point ((764)+1))/2) ≤ payment (764)
    have hp : payment 764 = (2780987597928:ℝ)/1000000000000 := rfl
    have hx : (point 764+point 765)/2 = (2799083:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_764
  · change upperValue ((point (765)+point ((765)+1))/2) ≤ payment (765)
    have hp : payment 765 = (2777582215064:ℝ)/1000000000000 := rfl
    have hx : (point 765+point 766)/2 = (2801137:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_765
  · change upperValue ((point (766)+point ((766)+1))/2) ≤ payment (766)
    have hp : payment 766 = (2774180952267:ℝ)/1000000000000 := rfl
    have hx : (point 766+point 767)/2 = (934397:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_766
  · change upperValue ((point (767)+point ((767)+1))/2) ≤ payment (767)
    have hp : payment 767 = (2770783799860:ℝ)/1000000000000 := rfl
    have hx : (point 767+point 768)/2 = (2805245:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_767
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_047
