import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints042
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_042 (j : Fin 16) : upperValue ((point (16*42+j.val)+point ((16*42+j.val)+1))/2) ≤ payment (16*42+j.val) := by
  fin_cases j
  · change upperValue ((point (672)+point ((672)+1))/2) ≤ payment (672)
    have hp : payment 672 = (3113300968577:ℝ)/1000000000000 := rfl
    have hx : (point 672+point 673)/2 = (2610115:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_672
  · change upperValue ((point (673)+point ((673)+1))/2) ≤ payment (673)
    have hp : payment 673 = (3109471056822:ℝ)/1000000000000 := rfl
    have hx : (point 673+point 674)/2 = (870723:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_673
  · change upperValue ((point (674)+point ((674)+1))/2) ≤ payment (674)
    have hp : payment 674 = (3105646289632:ℝ)/1000000000000 := rfl
    have hx : (point 674+point 675)/2 = (2614223:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_674
  · change upperValue ((point (675)+point ((675)+1))/2) ≤ payment (675)
    have hp : payment 675 = (3101826654271:ℝ)/1000000000000 := rfl
    have hx : (point 675+point 676)/2 = (2616277:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_675
  · change upperValue ((point (676)+point ((676)+1))/2) ≤ payment (676)
    have hp : payment 676 = (3098012138039:ℝ)/1000000000000 := rfl
    have hx : (point 676+point 677)/2 = (872777:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_676
  · change upperValue ((point (677)+point ((677)+1))/2) ≤ payment (677)
    have hp : payment 677 = (3094202728277:ℝ)/1000000000000 := rfl
    have hx : (point 677+point 678)/2 = (2620385:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_677
  · change upperValue ((point (678)+point ((678)+1))/2) ≤ payment (678)
    have hp : payment 678 = (3090398412364:ℝ)/1000000000000 := rfl
    have hx : (point 678+point 679)/2 = (2622439:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_678
  · change upperValue ((point (679)+point ((679)+1))/2) ≤ payment (679)
    have hp : payment 679 = (3086599177719:ℝ)/1000000000000 := rfl
    have hx : (point 679+point 680)/2 = (874831:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_679
  · change upperValue ((point (680)+point ((680)+1))/2) ≤ payment (680)
    have hp : payment 680 = (3082805011799:ℝ)/1000000000000 := rfl
    have hx : (point 680+point 681)/2 = (2626547:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_680
  · change upperValue ((point (681)+point ((681)+1))/2) ≤ payment (681)
    have hp : payment 681 = (3079015902100:ℝ)/1000000000000 := rfl
    have hx : (point 681+point 682)/2 = (2628601:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_681
  · change upperValue ((point (682)+point ((682)+1))/2) ≤ payment (682)
    have hp : payment 682 = (3075231836157:ℝ)/1000000000000 := rfl
    have hx : (point 682+point 683)/2 = (876885:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_682
  · change upperValue ((point (683)+point ((683)+1))/2) ≤ payment (683)
    have hp : payment 683 = (3071452801542:ℝ)/1000000000000 := rfl
    have hx : (point 683+point 684)/2 = (2632709:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_683
  · change upperValue ((point (684)+point ((684)+1))/2) ≤ payment (684)
    have hp : payment 684 = (3067678785867:ℝ)/1000000000000 := rfl
    have hx : (point 684+point 685)/2 = (2634763:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_684
  · change upperValue ((point (685)+point ((685)+1))/2) ≤ payment (685)
    have hp : payment 685 = (3063909776781:ℝ)/1000000000000 := rfl
    have hx : (point 685+point 686)/2 = (878939:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_685
  · change upperValue ((point (686)+point ((686)+1))/2) ≤ payment (686)
    have hp : payment 686 = (3060145761970:ℝ)/1000000000000 := rfl
    have hx : (point 686+point 687)/2 = (2638871:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_686
  · change upperValue ((point (687)+point ((687)+1))/2) ≤ payment (687)
    have hp : payment 687 = (3056386729160:ℝ)/1000000000000 := rfl
    have hx : (point 687+point 688)/2 = (2640925:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_687
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_042
