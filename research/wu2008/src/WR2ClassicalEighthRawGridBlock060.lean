import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints060
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_060 (j : Fin 16) : upperValue ((point (16*60+j.val)+point ((16*60+j.val)+1))/2) ≤ payment (16*60+j.val) := by
  fin_cases j
  · change upperValue ((point (960)+point ((960)+1))/2) ≤ payment (960)
    have hp : payment 960 = (2181756698140:ℝ)/1000000000000 := rfl
    have hx : (point 960+point 961)/2 = (3201667:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_960
  · change upperValue ((point (961)+point ((961)+1))/2) ≤ payment (961)
    have hp : payment 961 = (2179002992542:ℝ)/1000000000000 := rfl
    have hx : (point 961+point 962)/2 = (1067907:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_961
  · change upperValue ((point (962)+point ((962)+1))/2) ≤ payment (962)
    have hp : payment 962 = (2176251936656:ℝ)/1000000000000 := rfl
    have hx : (point 962+point 963)/2 = (3205775:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_962
  · change upperValue ((point (963)+point ((963)+1))/2) ≤ payment (963)
    have hp : payment 963 = (2173503524733:ℝ)/1000000000000 := rfl
    have hx : (point 963+point 964)/2 = (3207829:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_963
  · change upperValue ((point (964)+point ((964)+1))/2) ≤ payment (964)
    have hp : payment 964 = (2170757751041:ℝ)/1000000000000 := rfl
    have hx : (point 964+point 965)/2 = (1069961:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_964
  · change upperValue ((point (965)+point ((965)+1))/2) ≤ payment (965)
    have hp : payment 965 = (2168014609862:ℝ)/1000000000000 := rfl
    have hx : (point 965+point 966)/2 = (3211937:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_965
  · change upperValue ((point (966)+point ((966)+1))/2) ≤ payment (966)
    have hp : payment 966 = (2165274095492:ℝ)/1000000000000 := rfl
    have hx : (point 966+point 967)/2 = (3213991:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_966
  · change upperValue ((point (967)+point ((967)+1))/2) ≤ payment (967)
    have hp : payment 967 = (2162536202240:ℝ)/1000000000000 := rfl
    have hx : (point 967+point 968)/2 = (1072015:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_967
  · change upperValue ((point (968)+point ((968)+1))/2) ≤ payment (968)
    have hp : payment 968 = (2159800924430:ℝ)/1000000000000 := rfl
    have hx : (point 968+point 969)/2 = (3218099:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_968
  · change upperValue ((point (969)+point ((969)+1))/2) ≤ payment (969)
    have hp : payment 969 = (2157068256398:ℝ)/1000000000000 := rfl
    have hx : (point 969+point 970)/2 = (3220153:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_969
  · change upperValue ((point (970)+point ((970)+1))/2) ≤ payment (970)
    have hp : payment 970 = (2154338192496:ℝ)/1000000000000 := rfl
    have hx : (point 970+point 971)/2 = (1074069:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_970
  · change upperValue ((point (971)+point ((971)+1))/2) ≤ payment (971)
    have hp : payment 971 = (2151610727090:ℝ)/1000000000000 := rfl
    have hx : (point 971+point 972)/2 = (3224261:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_971
  · change upperValue ((point (972)+point ((972)+1))/2) ≤ payment (972)
    have hp : payment 972 = (2148885854557:ℝ)/1000000000000 := rfl
    have hx : (point 972+point 973)/2 = (3226315:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_972
  · change upperValue ((point (973)+point ((973)+1))/2) ≤ payment (973)
    have hp : payment 973 = (2146163569290:ℝ)/1000000000000 := rfl
    have hx : (point 973+point 974)/2 = (1076123:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_973
  · change upperValue ((point (974)+point ((974)+1))/2) ≤ payment (974)
    have hp : payment 974 = (2143443865695:ℝ)/1000000000000 := rfl
    have hx : (point 974+point 975)/2 = (3230423:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_974
  · change upperValue ((point (975)+point ((975)+1))/2) ≤ payment (975)
    have hp : payment 975 = (2140726738192:ℝ)/1000000000000 := rfl
    have hx : (point 975+point 976)/2 = (3232477:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_975
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_060
