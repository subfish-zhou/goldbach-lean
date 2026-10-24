import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints073
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_073 (j : Fin 16) : upperValue ((point (16*73+j.val)+point ((16*73+j.val)+1))/2) ≤ payment (16*73+j.val) := by
  fin_cases j
  · change upperValue ((point (1168)+point ((1168)+1))/2) ≤ payment (1168)
    have hp : payment 1168 = (1658476990870:ℝ)/1000000000000 := rfl
    have hx : (point 1168+point 1169)/2 = (1209633:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1168
  · change upperValue ((point (1169)+point ((1169)+1))/2) ≤ payment (1169)
    have hp : payment 1169 = (1656168558692:ℝ)/1000000000000 := rfl
    have hx : (point 1169+point 1170)/2 = (3630953:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1169
  · change upperValue ((point (1170)+point ((1170)+1))/2) ≤ payment (1170)
    have hp : payment 1170 = (1653861828013:ℝ)/1000000000000 := rfl
    have hx : (point 1170+point 1171)/2 = (3633007:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1170
  · change upperValue ((point (1171)+point ((1171)+1))/2) ≤ payment (1171)
    have hp : payment 1171 = (1651556795244:ℝ)/1000000000000 := rfl
    have hx : (point 1171+point 1172)/2 = (1211687:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1171
  · change upperValue ((point (1172)+point ((1172)+1))/2) ≤ payment (1172)
    have hp : payment 1172 = (1649253456803:ℝ)/1000000000000 := rfl
    have hx : (point 1172+point 1173)/2 = (3637115:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1172
  · change upperValue ((point (1173)+point ((1173)+1))/2) ≤ payment (1173)
    have hp : payment 1173 = (1646951809113:ℝ)/1000000000000 := rfl
    have hx : (point 1173+point 1174)/2 = (3639169:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1173
  · change upperValue ((point (1174)+point ((1174)+1))/2) ≤ payment (1174)
    have hp : payment 1174 = (1644651848609:ℝ)/1000000000000 := rfl
    have hx : (point 1174+point 1175)/2 = (1213741:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1174
  · change upperValue ((point (1175)+point ((1175)+1))/2) ≤ payment (1175)
    have hp : payment 1175 = (1642353571729:ℝ)/1000000000000 := rfl
    have hx : (point 1175+point 1176)/2 = (3643277:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1175
  · change upperValue ((point (1176)+point ((1176)+1))/2) ≤ payment (1176)
    have hp : payment 1176 = (1640056974921:ℝ)/1000000000000 := rfl
    have hx : (point 1176+point 1177)/2 = (3645331:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1176
  · change upperValue ((point (1177)+point ((1177)+1))/2) ≤ payment (1177)
    have hp : payment 1177 = (1637762054639:ℝ)/1000000000000 := rfl
    have hx : (point 1177+point 1178)/2 = (1215795:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1177
  · change upperValue ((point (1178)+point ((1178)+1))/2) ≤ payment (1178)
    have hp : payment 1178 = (1635468807345:ℝ)/1000000000000 := rfl
    have hx : (point 1178+point 1179)/2 = (3649439:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1178
  · change upperValue ((point (1179)+point ((1179)+1))/2) ≤ payment (1179)
    have hp : payment 1179 = (1633177229508:ℝ)/1000000000000 := rfl
    have hx : (point 1179+point 1180)/2 = (3651493:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1179
  · change upperValue ((point (1180)+point ((1180)+1))/2) ≤ payment (1180)
    have hp : payment 1180 = (1630887317605:ℝ)/1000000000000 := rfl
    have hx : (point 1180+point 1181)/2 = (1217849:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1180
  · change upperValue ((point (1181)+point ((1181)+1))/2) ≤ payment (1181)
    have hp : payment 1181 = (1628599068119:ℝ)/1000000000000 := rfl
    have hx : (point 1181+point 1182)/2 = (3655601:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1181
  · change upperValue ((point (1182)+point ((1182)+1))/2) ≤ payment (1182)
    have hp : payment 1182 = (1626312477541:ℝ)/1000000000000 := rfl
    have hx : (point 1182+point 1183)/2 = (3657655:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1182
  · change upperValue ((point (1183)+point ((1183)+1))/2) ≤ payment (1183)
    have hp : payment 1183 = (1624027542368:ℝ)/1000000000000 := rfl
    have hx : (point 1183+point 1184)/2 = (1219903:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1183
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_073
