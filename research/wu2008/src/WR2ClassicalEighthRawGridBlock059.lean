import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints059
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_059 (j : Fin 16) : upperValue ((point (16*59+j.val)+point ((16*59+j.val)+1))/2) ≤ payment (16*59+j.val) := by
  fin_cases j
  · change upperValue ((point (944)+point ((944)+1))/2) ≤ payment (944)
    have hp : payment 944 = (2226181092905:ℝ)/1000000000000 := rfl
    have hx : (point 944+point 945)/2 = (3168803:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_944
  · change upperValue ((point (945)+point ((945)+1))/2) ≤ payment (945)
    have hp : payment 945 = (2223384198718:ℝ)/1000000000000 := rfl
    have hx : (point 945+point 946)/2 = (3170857:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_945
  · change upperValue ((point (946)+point ((946)+1))/2) ≤ payment (946)
    have hp : payment 946 = (2220590048143:ℝ)/1000000000000 := rfl
    have hx : (point 946+point 947)/2 = (1057637:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_946
  · change upperValue ((point (947)+point ((947)+1))/2) ≤ payment (947)
    have hp : payment 947 = (2217798635200:ℝ)/1000000000000 := rfl
    have hx : (point 947+point 948)/2 = (3174965:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_947
  · change upperValue ((point (948)+point ((948)+1))/2) ≤ payment (948)
    have hp : payment 948 = (2215009953928:ℝ)/1000000000000 := rfl
    have hx : (point 948+point 949)/2 = (3177019:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_948
  · change upperValue ((point (949)+point ((949)+1))/2) ≤ payment (949)
    have hp : payment 949 = (2212223998375:ℝ)/1000000000000 := rfl
    have hx : (point 949+point 950)/2 = (1059691:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_949
  · change upperValue ((point (950)+point ((950)+1))/2) ≤ payment (950)
    have hp : payment 950 = (2209440762609:ℝ)/1000000000000 := rfl
    have hx : (point 950+point 951)/2 = (3181127:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_950
  · change upperValue ((point (951)+point ((951)+1))/2) ≤ payment (951)
    have hp : payment 951 = (2206660240710:ℝ)/1000000000000 := rfl
    have hx : (point 951+point 952)/2 = (3183181:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_951
  · change upperValue ((point (952)+point ((952)+1))/2) ≤ payment (952)
    have hp : payment 952 = (2203882426773:ℝ)/1000000000000 := rfl
    have hx : (point 952+point 953)/2 = (1061745:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_952
  · change upperValue ((point (953)+point ((953)+1))/2) ≤ payment (953)
    have hp : payment 953 = (2201107314908:ℝ)/1000000000000 := rfl
    have hx : (point 953+point 954)/2 = (3187289:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_953
  · change upperValue ((point (954)+point ((954)+1))/2) ≤ payment (954)
    have hp : payment 954 = (2198334899239:ℝ)/1000000000000 := rfl
    have hx : (point 954+point 955)/2 = (3189343:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_954
  · change upperValue ((point (955)+point ((955)+1))/2) ≤ payment (955)
    have hp : payment 955 = (2195565173905:ℝ)/1000000000000 := rfl
    have hx : (point 955+point 956)/2 = (1063799:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_955
  · change upperValue ((point (956)+point ((956)+1))/2) ≤ payment (956)
    have hp : payment 956 = (2192798133061:ℝ)/1000000000000 := rfl
    have hx : (point 956+point 957)/2 = (3193451:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_956
  · change upperValue ((point (957)+point ((957)+1))/2) ≤ payment (957)
    have hp : payment 957 = (2190033770872:ℝ)/1000000000000 := rfl
    have hx : (point 957+point 958)/2 = (3195505:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_957
  · change upperValue ((point (958)+point ((958)+1))/2) ≤ payment (958)
    have hp : payment 958 = (2187272081522:ℝ)/1000000000000 := rfl
    have hx : (point 958+point 959)/2 = (1065853:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_958
  · change upperValue ((point (959)+point ((959)+1))/2) ≤ payment (959)
    have hp : payment 959 = (2184513059208:ℝ)/1000000000000 := rfl
    have hx : (point 959+point 960)/2 = (3199613:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_959
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_059
