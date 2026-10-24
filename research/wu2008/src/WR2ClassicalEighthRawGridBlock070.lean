import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints070
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_070 (j : Fin 16) : upperValue ((point (16*70+j.val)+point ((16*70+j.val)+1))/2) ≤ payment (16*70+j.val) := by
  fin_cases j
  · change upperValue ((point (1120)+point ((1120)+1))/2) ≤ payment (1120)
    have hp : payment 1120 = (1771354971916:ℝ)/1000000000000 := rfl
    have hx : (point 1120+point 1121)/2 = (1176769:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1120
  · change upperValue ((point (1121)+point ((1121)+1))/2) ≤ payment (1121)
    have hp : payment 1121 = (1768960495024:ℝ)/1000000000000 := rfl
    have hx : (point 1121+point 1122)/2 = (3532361:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1121
  · change upperValue ((point (1122)+point ((1122)+1))/2) ≤ payment (1122)
    have hp : payment 1122 = (1766567901119:ℝ)/1000000000000 := rfl
    have hx : (point 1122+point 1123)/2 = (3534415:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1122
  · change upperValue ((point (1123)+point ((1123)+1))/2) ≤ payment (1123)
    have hp : payment 1123 = (1764177186228:ℝ)/1000000000000 := rfl
    have hx : (point 1123+point 1124)/2 = (1178823:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1123
  · change upperValue ((point (1124)+point ((1124)+1))/2) ≤ payment (1124)
    have hp : payment 1124 = (1761788346385:ℝ)/1000000000000 := rfl
    have hx : (point 1124+point 1125)/2 = (3538523:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1124
  · change upperValue ((point (1125)+point ((1125)+1))/2) ≤ payment (1125)
    have hp : payment 1125 = (1759401377636:ℝ)/1000000000000 := rfl
    have hx : (point 1125+point 1126)/2 = (3540577:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1125
  · change upperValue ((point (1126)+point ((1126)+1))/2) ≤ payment (1126)
    have hp : payment 1126 = (1757016276031:ℝ)/1000000000000 := rfl
    have hx : (point 1126+point 1127)/2 = (1180877:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1126
  · change upperValue ((point (1127)+point ((1127)+1))/2) ≤ payment (1127)
    have hp : payment 1127 = (1754633037631:ℝ)/1000000000000 := rfl
    have hx : (point 1127+point 1128)/2 = (3544685:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1127
  · change upperValue ((point (1128)+point ((1128)+1))/2) ≤ payment (1128)
    have hp : payment 1128 = (1752251658507:ℝ)/1000000000000 := rfl
    have hx : (point 1128+point 1129)/2 = (3546739:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1128
  · change upperValue ((point (1129)+point ((1129)+1))/2) ≤ payment (1129)
    have hp : payment 1129 = (1749872134735:ℝ)/1000000000000 := rfl
    have hx : (point 1129+point 1130)/2 = (1182931:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1129
  · change upperValue ((point (1130)+point ((1130)+1))/2) ≤ payment (1130)
    have hp : payment 1130 = (1747494462401:ℝ)/1000000000000 := rfl
    have hx : (point 1130+point 1131)/2 = (3550847:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1130
  · change upperValue ((point (1131)+point ((1131)+1))/2) ≤ payment (1131)
    have hp : payment 1131 = (1745118637601:ℝ)/1000000000000 := rfl
    have hx : (point 1131+point 1132)/2 = (3552901:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1131
  · change upperValue ((point (1132)+point ((1132)+1))/2) ≤ payment (1132)
    have hp : payment 1132 = (1742744656436:ℝ)/1000000000000 := rfl
    have hx : (point 1132+point 1133)/2 = (1184985:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1132
  · change upperValue ((point (1133)+point ((1133)+1))/2) ≤ payment (1133)
    have hp : payment 1133 = (1740372515019:ℝ)/1000000000000 := rfl
    have hx : (point 1133+point 1134)/2 = (3557009:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1133
  · change upperValue ((point (1134)+point ((1134)+1))/2) ≤ payment (1134)
    have hp : payment 1134 = (1738002209467:ℝ)/1000000000000 := rfl
    have hx : (point 1134+point 1135)/2 = (3559063:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1134
  · change upperValue ((point (1135)+point ((1135)+1))/2) ≤ payment (1135)
    have hp : payment 1135 = (1735633735910:ℝ)/1000000000000 := rfl
    have hx : (point 1135+point 1136)/2 = (1187039:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1135
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_070
