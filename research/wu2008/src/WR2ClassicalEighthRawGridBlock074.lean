import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints074
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_074 (j : Fin 16) : upperValue ((point (16*74+j.val)+point ((16*74+j.val)+1))/2) ≤ payment (16*74+j.val) := by
  fin_cases j
  · change upperValue ((point (1184)+point ((1184)+1))/2) ≤ payment (1184)
    have hp : payment 1184 = (1621744259106:ℝ)/1000000000000 := rfl
    have hx : (point 1184+point 1185)/2 = (3661763:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1184
  · change upperValue ((point (1185)+point ((1185)+1))/2) ≤ payment (1185)
    have hp : payment 1185 = (1619462624268:ℝ)/1000000000000 := rfl
    have hx : (point 1185+point 1186)/2 = (3663817:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1185
  · change upperValue ((point (1186)+point ((1186)+1))/2) ≤ payment (1186)
    have hp : payment 1186 = (1617182634372:ℝ)/1000000000000 := rfl
    have hx : (point 1186+point 1187)/2 = (1221957:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1186
  · change upperValue ((point (1187)+point ((1187)+1))/2) ≤ payment (1187)
    have hp : payment 1187 = (1614904285945:ℝ)/1000000000000 := rfl
    have hx : (point 1187+point 1188)/2 = (3667925:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1187
  · change upperValue ((point (1188)+point ((1188)+1))/2) ≤ payment (1188)
    have hp : payment 1188 = (1612627575521:ℝ)/1000000000000 := rfl
    have hx : (point 1188+point 1189)/2 = (3669979:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1188
  · change upperValue ((point (1189)+point ((1189)+1))/2) ≤ payment (1189)
    have hp : payment 1189 = (1610352499640:ℝ)/1000000000000 := rfl
    have hx : (point 1189+point 1190)/2 = (1224011:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1189
  · change upperValue ((point (1190)+point ((1190)+1))/2) ≤ payment (1190)
    have hp : payment 1190 = (1608079054850:ℝ)/1000000000000 := rfl
    have hx : (point 1190+point 1191)/2 = (3674087:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1190
  · change upperValue ((point (1191)+point ((1191)+1))/2) ≤ payment (1191)
    have hp : payment 1191 = (1605807237707:ℝ)/1000000000000 := rfl
    have hx : (point 1191+point 1192)/2 = (3676141:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1191
  · change upperValue ((point (1192)+point ((1192)+1))/2) ≤ payment (1192)
    have hp : payment 1192 = (1603537044770:ℝ)/1000000000000 := rfl
    have hx : (point 1192+point 1193)/2 = (1226065:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1192
  · change upperValue ((point (1193)+point ((1193)+1))/2) ≤ payment (1193)
    have hp : payment 1193 = (1601268472610:ℝ)/1000000000000 := rfl
    have hx : (point 1193+point 1194)/2 = (3680249:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1193
  · change upperValue ((point (1194)+point ((1194)+1))/2) ≤ payment (1194)
    have hp : payment 1194 = (1599001517803:ℝ)/1000000000000 := rfl
    have hx : (point 1194+point 1195)/2 = (3682303:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1194
  · change upperValue ((point (1195)+point ((1195)+1))/2) ≤ payment (1195)
    have hp : payment 1195 = (1596736176929:ℝ)/1000000000000 := rfl
    have hx : (point 1195+point 1196)/2 = (1228119:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1195
  · change upperValue ((point (1196)+point ((1196)+1))/2) ≤ payment (1196)
    have hp : payment 1196 = (1594472446580:ℝ)/1000000000000 := rfl
    have hx : (point 1196+point 1197)/2 = (3686411:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1196
  · change upperValue ((point (1197)+point ((1197)+1))/2) ≤ payment (1197)
    have hp : payment 1197 = (1592210323352:ℝ)/1000000000000 := rfl
    have hx : (point 1197+point 1198)/2 = (3688465:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1197
  · change upperValue ((point (1198)+point ((1198)+1))/2) ≤ payment (1198)
    have hp : payment 1198 = (1589949803848:ℝ)/1000000000000 := rfl
    have hx : (point 1198+point 1199)/2 = (1230173:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1198
  · change upperValue ((point (1199)+point ((1199)+1))/2) ≤ payment (1199)
    have hp : payment 1199 = (1587690884678:ℝ)/1000000000000 := rfl
    have hx : (point 1199+point 1200)/2 = (3692573:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1199
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_074
