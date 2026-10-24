import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints010
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_010 (j : Fin 16) : upperValue ((point (16*10+j.val)+point ((16*10+j.val)+1))/2) ≤ payment (16*10+j.val) := by
  fin_cases j
  · change upperValue ((point (160)+point ((160)+1))/2) ≤ payment (160)
    have hp : payment 160 = (6228625297800:ℝ)/1000000000000 := rfl
    have hx : (point 160+point 161)/2 = (519489:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_160
  · change upperValue ((point (161)+point ((161)+1))/2) ≤ payment (161)
    have hp : payment 161 = (6218744539529:ℝ)/1000000000000 := rfl
    have hx : (point 161+point 162)/2 = (1560521:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_161
  · change upperValue ((point (162)+point ((162)+1))/2) ≤ payment (162)
    have hp : payment 162 = (6208888727798:ℝ)/1000000000000 := rfl
    have hx : (point 162+point 163)/2 = (1562575:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_162
  · change upperValue ((point (163)+point ((163)+1))/2) ≤ payment (163)
    have hp : payment 163 = (6199057763683:ℝ)/1000000000000 := rfl
    have hx : (point 163+point 164)/2 = (521543:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_163
  · change upperValue ((point (164)+point ((164)+1))/2) ≤ payment (164)
    have hp : payment 164 = (6189251548777:ℝ)/1000000000000 := rfl
    have hx : (point 164+point 165)/2 = (1566683:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_164
  · change upperValue ((point (165)+point ((165)+1))/2) ≤ payment (165)
    have hp : payment 165 = (6179469985187:ℝ)/1000000000000 := rfl
    have hx : (point 165+point 166)/2 = (1568737:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_165
  · change upperValue ((point (166)+point ((166)+1))/2) ≤ payment (166)
    have hp : payment 166 = (6169712975534:ℝ)/1000000000000 := rfl
    have hx : (point 166+point 167)/2 = (523597:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_166
  · change upperValue ((point (167)+point ((167)+1))/2) ≤ payment (167)
    have hp : payment 167 = (6159980422946:ℝ)/1000000000000 := rfl
    have hx : (point 167+point 168)/2 = (1572845:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_167
  · change upperValue ((point (168)+point ((168)+1))/2) ≤ payment (168)
    have hp : payment 168 = (6150272231054:ℝ)/1000000000000 := rfl
    have hx : (point 168+point 169)/2 = (1574899:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_168
  · change upperValue ((point (169)+point ((169)+1))/2) ≤ payment (169)
    have hp : payment 169 = (6140588303994:ℝ)/1000000000000 := rfl
    have hx : (point 169+point 170)/2 = (525651:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_169
  · change upperValue ((point (170)+point ((170)+1))/2) ≤ payment (170)
    have hp : payment 170 = (6130928546398:ℝ)/1000000000000 := rfl
    have hx : (point 170+point 171)/2 = (1579007:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_170
  · change upperValue ((point (171)+point ((171)+1))/2) ≤ payment (171)
    have hp : payment 171 = (6121292863393:ℝ)/1000000000000 := rfl
    have hx : (point 171+point 172)/2 = (1581061:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_171
  · change upperValue ((point (172)+point ((172)+1))/2) ≤ payment (172)
    have hp : payment 172 = (6111681160598:ℝ)/1000000000000 := rfl
    have hx : (point 172+point 173)/2 = (527705:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_172
  · change upperValue ((point (173)+point ((173)+1))/2) ≤ payment (173)
    have hp : payment 173 = (6102093344122:ℝ)/1000000000000 := rfl
    have hx : (point 173+point 174)/2 = (1585169:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_173
  · change upperValue ((point (174)+point ((174)+1))/2) ≤ payment (174)
    have hp : payment 174 = (6092529320558:ℝ)/1000000000000 := rfl
    have hx : (point 174+point 175)/2 = (1587223:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_174
  · change upperValue ((point (175)+point ((175)+1))/2) ≤ payment (175)
    have hp : payment 175 = (6082988996981:ℝ)/1000000000000 := rfl
    have hx : (point 175+point 176)/2 = (529759:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_175
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_010
