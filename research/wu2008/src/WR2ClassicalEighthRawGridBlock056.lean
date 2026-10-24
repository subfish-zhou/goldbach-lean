import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints056
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_056 (j : Fin 16) : upperValue ((point (16*56+j.val)+point ((16*56+j.val)+1))/2) ≤ payment (16*56+j.val) := by
  fin_cases j
  · change upperValue ((point (896)+point ((896)+1))/2) ≤ payment (896)
    have hp : payment 896 = (2363779525463:ℝ)/1000000000000 := rfl
    have hx : (point 896+point 897)/2 = (3070211:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_896
  · change upperValue ((point (897)+point ((897)+1))/2) ≤ payment (897)
    have hp : payment 897 = (2360843603208:ℝ)/1000000000000 := rfl
    have hx : (point 897+point 898)/2 = (3072265:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_897
  · change upperValue ((point (898)+point ((898)+1))/2) ≤ payment (898)
    have hp : payment 898 = (2357910730014:ℝ)/1000000000000 := rfl
    have hx : (point 898+point 899)/2 = (1024773:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_898
  · change upperValue ((point (899)+point ((899)+1))/2) ≤ payment (899)
    have hp : payment 899 = (2354980899127:ℝ)/1000000000000 := rfl
    have hx : (point 899+point 900)/2 = (3076373:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_899
  · change upperValue ((point (900)+point ((900)+1))/2) ≤ payment (900)
    have hp : payment 900 = (2352054103811:ℝ)/1000000000000 := rfl
    have hx : (point 900+point 901)/2 = (3078427:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_900
  · change upperValue ((point (901)+point ((901)+1))/2) ≤ payment (901)
    have hp : payment 901 = (2349130337350:ℝ)/1000000000000 := rfl
    have hx : (point 901+point 902)/2 = (1026827:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_901
  · change upperValue ((point (902)+point ((902)+1))/2) ≤ payment (902)
    have hp : payment 902 = (2346209593041:ℝ)/1000000000000 := rfl
    have hx : (point 902+point 903)/2 = (3082535:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_902
  · change upperValue ((point (903)+point ((903)+1))/2) ≤ payment (903)
    have hp : payment 903 = (2343291864202:ℝ)/1000000000000 := rfl
    have hx : (point 903+point 904)/2 = (3084589:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_903
  · change upperValue ((point (904)+point ((904)+1))/2) ≤ payment (904)
    have hp : payment 904 = (2340377144166:ℝ)/1000000000000 := rfl
    have hx : (point 904+point 905)/2 = (1028881:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_904
  · change upperValue ((point (905)+point ((905)+1))/2) ≤ payment (905)
    have hp : payment 905 = (2337465426284:ℝ)/1000000000000 := rfl
    have hx : (point 905+point 906)/2 = (3088697:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_905
  · change upperValue ((point (906)+point ((906)+1))/2) ≤ payment (906)
    have hp : payment 906 = (2334556703923:ℝ)/1000000000000 := rfl
    have hx : (point 906+point 907)/2 = (3090751:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_906
  · change upperValue ((point (907)+point ((907)+1))/2) ≤ payment (907)
    have hp : payment 907 = (2331650970469:ℝ)/1000000000000 := rfl
    have hx : (point 907+point 908)/2 = (1030935:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_907
  · change upperValue ((point (908)+point ((908)+1))/2) ≤ payment (908)
    have hp : payment 908 = (2328748219324:ℝ)/1000000000000 := rfl
    have hx : (point 908+point 909)/2 = (3094859:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_908
  · change upperValue ((point (909)+point ((909)+1))/2) ≤ payment (909)
    have hp : payment 909 = (2325848443905:ℝ)/1000000000000 := rfl
    have hx : (point 909+point 910)/2 = (3096913:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_909
  · change upperValue ((point (910)+point ((910)+1))/2) ≤ payment (910)
    have hp : payment 910 = (2322951637650:ℝ)/1000000000000 := rfl
    have hx : (point 910+point 911)/2 = (1032989:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_910
  · change upperValue ((point (911)+point ((911)+1))/2) ≤ payment (911)
    have hp : payment 911 = (2320057794010:ℝ)/1000000000000 := rfl
    have hx : (point 911+point 912)/2 = (3101021:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_911
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_056
