import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints071
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_071 (j : Fin 16) : upperValue ((point (16*71+j.val)+point ((16*71+j.val)+1))/2) ≤ payment (16*71+j.val) := by
  fin_cases j
  · change upperValue ((point (1136)+point ((1136)+1))/2) ≤ payment (1136)
    have hp : payment 1136 = (1733267090483:ℝ)/1000000000000 := rfl
    have hx : (point 1136+point 1137)/2 = (3563171:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1136
  · change upperValue ((point (1137)+point ((1137)+1))/2) ≤ payment (1137)
    have hp : payment 1137 = (1730902269331:ℝ)/1000000000000 := rfl
    have hx : (point 1137+point 1138)/2 = (3565225:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1137
  · change upperValue ((point (1138)+point ((1138)+1))/2) ≤ payment (1138)
    have hp : payment 1138 = (1728539268605:ℝ)/1000000000000 := rfl
    have hx : (point 1138+point 1139)/2 = (1189093:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1138
  · change upperValue ((point (1139)+point ((1139)+1))/2) ≤ payment (1139)
    have hp : payment 1139 = (1726178084467:ℝ)/1000000000000 := rfl
    have hx : (point 1139+point 1140)/2 = (3569333:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1139
  · change upperValue ((point (1140)+point ((1140)+1))/2) ≤ payment (1140)
    have hp : payment 1140 = (1723818713085:ℝ)/1000000000000 := rfl
    have hx : (point 1140+point 1141)/2 = (3571387:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1140
  · change upperValue ((point (1141)+point ((1141)+1))/2) ≤ payment (1141)
    have hp : payment 1141 = (1721461150637:ℝ)/1000000000000 := rfl
    have hx : (point 1141+point 1142)/2 = (1191147:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1141
  · change upperValue ((point (1142)+point ((1142)+1))/2) ≤ payment (1142)
    have hp : payment 1142 = (1719105393306:ℝ)/1000000000000 := rfl
    have hx : (point 1142+point 1143)/2 = (3575495:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1142
  · change upperValue ((point (1143)+point ((1143)+1))/2) ≤ payment (1143)
    have hp : payment 1143 = (1716751437287:ℝ)/1000000000000 := rfl
    have hx : (point 1143+point 1144)/2 = (3577549:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1143
  · change upperValue ((point (1144)+point ((1144)+1))/2) ≤ payment (1144)
    have hp : payment 1144 = (1714399278781:ℝ)/1000000000000 := rfl
    have hx : (point 1144+point 1145)/2 = (1193201:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1144
  · change upperValue ((point (1145)+point ((1145)+1))/2) ≤ payment (1145)
    have hp : payment 1145 = (1712048913997:ℝ)/1000000000000 := rfl
    have hx : (point 1145+point 1146)/2 = (3581657:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1145
  · change upperValue ((point (1146)+point ((1146)+1))/2) ≤ payment (1146)
    have hp : payment 1146 = (1709700339152:ℝ)/1000000000000 := rfl
    have hx : (point 1146+point 1147)/2 = (3583711:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1146
  · change upperValue ((point (1147)+point ((1147)+1))/2) ≤ payment (1147)
    have hp : payment 1147 = (1707353550472:ℝ)/1000000000000 := rfl
    have hx : (point 1147+point 1148)/2 = (1195255:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1147
  · change upperValue ((point (1148)+point ((1148)+1))/2) ≤ payment (1148)
    have hp : payment 1148 = (1705008544189:ℝ)/1000000000000 := rfl
    have hx : (point 1148+point 1149)/2 = (3587819:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1148
  · change upperValue ((point (1149)+point ((1149)+1))/2) ≤ payment (1149)
    have hp : payment 1149 = (1702665316545:ℝ)/1000000000000 := rfl
    have hx : (point 1149+point 1150)/2 = (3589873:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1149
  · change upperValue ((point (1150)+point ((1150)+1))/2) ≤ payment (1150)
    have hp : payment 1150 = (1700323863789:ℝ)/1000000000000 := rfl
    have hx : (point 1150+point 1151)/2 = (1197309:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1150
  · change upperValue ((point (1151)+point ((1151)+1))/2) ≤ payment (1151)
    have hp : payment 1151 = (1697984182179:ℝ)/1000000000000 := rfl
    have hx : (point 1151+point 1152)/2 = (3593981:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1151
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_071
