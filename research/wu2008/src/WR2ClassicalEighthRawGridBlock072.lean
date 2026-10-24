import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints072
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_072 (j : Fin 16) : upperValue ((point (16*72+j.val)+point ((16*72+j.val)+1))/2) ≤ payment (16*72+j.val) := by
  fin_cases j
  · change upperValue ((point (1152)+point ((1152)+1))/2) ≤ payment (1152)
    have hp : payment 1152 = (1695646267978:ℝ)/1000000000000 := rfl
    have hx : (point 1152+point 1153)/2 = (3596035:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1152
  · change upperValue ((point (1153)+point ((1153)+1))/2) ≤ payment (1153)
    have hp : payment 1153 = (1693310117460:ℝ)/1000000000000 := rfl
    have hx : (point 1153+point 1154)/2 = (1199363:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1153
  · change upperValue ((point (1154)+point ((1154)+1))/2) ≤ payment (1154)
    have hp : payment 1154 = (1690975726906:ℝ)/1000000000000 := rfl
    have hx : (point 1154+point 1155)/2 = (3600143:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1154
  · change upperValue ((point (1155)+point ((1155)+1))/2) ≤ payment (1155)
    have hp : payment 1155 = (1688643092603:ℝ)/1000000000000 := rfl
    have hx : (point 1155+point 1156)/2 = (3602197:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1155
  · change upperValue ((point (1156)+point ((1156)+1))/2) ≤ payment (1156)
    have hp : payment 1156 = (1686312210849:ℝ)/1000000000000 := rfl
    have hx : (point 1156+point 1157)/2 = (1201417:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1156
  · change upperValue ((point (1157)+point ((1157)+1))/2) ≤ payment (1157)
    have hp : payment 1157 = (1683983077946:ℝ)/1000000000000 := rfl
    have hx : (point 1157+point 1158)/2 = (3606305:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1157
  · change upperValue ((point (1158)+point ((1158)+1))/2) ≤ payment (1158)
    have hp : payment 1158 = (1681655690206:ℝ)/1000000000000 := rfl
    have hx : (point 1158+point 1159)/2 = (3608359:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1158
  · change upperValue ((point (1159)+point ((1159)+1))/2) ≤ payment (1159)
    have hp : payment 1159 = (1679330043950:ℝ)/1000000000000 := rfl
    have hx : (point 1159+point 1160)/2 = (1203471:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1159
  · change upperValue ((point (1160)+point ((1160)+1))/2) ≤ payment (1160)
    have hp : payment 1160 = (1677006135504:ℝ)/1000000000000 := rfl
    have hx : (point 1160+point 1161)/2 = (3612467:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1160
  · change upperValue ((point (1161)+point ((1161)+1))/2) ≤ payment (1161)
    have hp : payment 1161 = (1674683961202:ℝ)/1000000000000 := rfl
    have hx : (point 1161+point 1162)/2 = (3614521:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1161
  · change upperValue ((point (1162)+point ((1162)+1))/2) ≤ payment (1162)
    have hp : payment 1162 = (1672363517388:ℝ)/1000000000000 := rfl
    have hx : (point 1162+point 1163)/2 = (1205525:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1162
  · change upperValue ((point (1163)+point ((1163)+1))/2) ≤ payment (1163)
    have hp : payment 1163 = (1670044800411:ℝ)/1000000000000 := rfl
    have hx : (point 1163+point 1164)/2 = (3618629:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1163
  · change upperValue ((point (1164)+point ((1164)+1))/2) ≤ payment (1164)
    have hp : payment 1164 = (1667727806630:ℝ)/1000000000000 := rfl
    have hx : (point 1164+point 1165)/2 = (3620683:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1164
  · change upperValue ((point (1165)+point ((1165)+1))/2) ≤ payment (1165)
    have hp : payment 1165 = (1665412532408:ℝ)/1000000000000 := rfl
    have hx : (point 1165+point 1166)/2 = (1207579:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1165
  · change upperValue ((point (1166)+point ((1166)+1))/2) ≤ payment (1166)
    have hp : payment 1166 = (1663098974119:ℝ)/1000000000000 := rfl
    have hx : (point 1166+point 1167)/2 = (3624791:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1166
  · change upperValue ((point (1167)+point ((1167)+1))/2) ≤ payment (1167)
    have hp : payment 1167 = (1660787128144:ℝ)/1000000000000 := rfl
    have hx : (point 1167+point 1168)/2 = (3626845:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1167
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_072
