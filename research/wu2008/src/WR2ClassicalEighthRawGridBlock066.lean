import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints066
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_066 (j : Fin 16) : upperValue ((point (16*66+j.val)+point ((16*66+j.val)+1))/2) ≤ payment (16*66+j.val) := by
  fin_cases j
  · change upperValue ((point (1056)+point ((1056)+1))/2) ≤ payment (1056)
    have hp : payment 1056 = (1928706767907:ℝ)/1000000000000 := rfl
    have hx : (point 1056+point 1057)/2 = (3398851:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1056
  · change upperValue ((point (1057)+point ((1057)+1))/2) ≤ payment (1057)
    have hp : payment 1057 = (1926183102833:ℝ)/1000000000000 := rfl
    have hx : (point 1057+point 1058)/2 = (1133635:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1057
  · change upperValue ((point (1058)+point ((1058)+1))/2) ≤ payment (1058)
    have hp : payment 1058 = (1923661594096:ℝ)/1000000000000 := rfl
    have hx : (point 1058+point 1059)/2 = (3402959:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1058
  · change upperValue ((point (1059)+point ((1059)+1))/2) ≤ payment (1059)
    have hp : payment 1059 = (1921142237116:ℝ)/1000000000000 := rfl
    have hx : (point 1059+point 1060)/2 = (3405013:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1059
  · change upperValue ((point (1060)+point ((1060)+1))/2) ≤ payment (1060)
    have hp : payment 1060 = (1918625027325:ℝ)/1000000000000 := rfl
    have hx : (point 1060+point 1061)/2 = (1135689:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1060
  · change upperValue ((point (1061)+point ((1061)+1))/2) ≤ payment (1061)
    have hp : payment 1061 = (1916109960164:ℝ)/1000000000000 := rfl
    have hx : (point 1061+point 1062)/2 = (3409121:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1061
  · change upperValue ((point (1062)+point ((1062)+1))/2) ≤ payment (1062)
    have hp : payment 1062 = (1913597031086:ℝ)/1000000000000 := rfl
    have hx : (point 1062+point 1063)/2 = (3411175:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1062
  · change upperValue ((point (1063)+point ((1063)+1))/2) ≤ payment (1063)
    have hp : payment 1063 = (1911086235554:ℝ)/1000000000000 := rfl
    have hx : (point 1063+point 1064)/2 = (1137743:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1063
  · change upperValue ((point (1064)+point ((1064)+1))/2) ≤ payment (1064)
    have hp : payment 1064 = (1908577569039:ℝ)/1000000000000 := rfl
    have hx : (point 1064+point 1065)/2 = (3415283:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1064
  · change upperValue ((point (1065)+point ((1065)+1))/2) ≤ payment (1065)
    have hp : payment 1065 = (1906071027025:ℝ)/1000000000000 := rfl
    have hx : (point 1065+point 1066)/2 = (3417337:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1065
  · change upperValue ((point (1066)+point ((1066)+1))/2) ≤ payment (1066)
    have hp : payment 1066 = (1903566605005:ℝ)/1000000000000 := rfl
    have hx : (point 1066+point 1067)/2 = (1139797:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1066
  · change upperValue ((point (1067)+point ((1067)+1))/2) ≤ payment (1067)
    have hp : payment 1067 = (1901064298482:ℝ)/1000000000000 := rfl
    have hx : (point 1067+point 1068)/2 = (3421445:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1067
  · change upperValue ((point (1068)+point ((1068)+1))/2) ≤ payment (1068)
    have hp : payment 1068 = (1898564102970:ℝ)/1000000000000 := rfl
    have hx : (point 1068+point 1069)/2 = (3423499:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1068
  · change upperValue ((point (1069)+point ((1069)+1))/2) ≤ payment (1069)
    have hp : payment 1069 = (1896066013993:ℝ)/1000000000000 := rfl
    have hx : (point 1069+point 1070)/2 = (1141851:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1069
  · change upperValue ((point (1070)+point ((1070)+1))/2) ≤ payment (1070)
    have hp : payment 1070 = (1893570027083:ℝ)/1000000000000 := rfl
    have hx : (point 1070+point 1071)/2 = (3427607:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1070
  · change upperValue ((point (1071)+point ((1071)+1))/2) ≤ payment (1071)
    have hp : payment 1071 = (1891076137786:ℝ)/1000000000000 := rfl
    have hx : (point 1071+point 1072)/2 = (3429661:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1071
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_066
