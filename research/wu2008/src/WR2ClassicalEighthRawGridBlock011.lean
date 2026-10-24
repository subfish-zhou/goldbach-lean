import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints011
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_011 (j : Fin 16) : upperValue ((point (16*11+j.val)+point ((16*11+j.val)+1))/2) ≤ payment (16*11+j.val) := by
  fin_cases j
  · change upperValue ((point (176)+point ((176)+1))/2) ≤ payment (176)
    have hp : payment 176 = (6073472280948:ℝ)/1000000000000 := rfl
    have hx : (point 176+point 177)/2 = (1591331:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_176
  · change upperValue ((point (177)+point ((177)+1))/2) ≤ payment (177)
    have hp : payment 177 = (6063979080488:ℝ)/1000000000000 := rfl
    have hx : (point 177+point 178)/2 = (1593385:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_177
  · change upperValue ((point (178)+point ((178)+1))/2) ≤ payment (178)
    have hp : payment 178 = (6054509304106:ℝ)/1000000000000 := rfl
    have hx : (point 178+point 179)/2 = (531813:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_178
  · change upperValue ((point (179)+point ((179)+1))/2) ≤ payment (179)
    have hp : payment 179 = (6045062860776:ℝ)/1000000000000 := rfl
    have hx : (point 179+point 180)/2 = (1597493:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_179
  · change upperValue ((point (180)+point ((180)+1))/2) ≤ payment (180)
    have hp : payment 180 = (6035639659940:ℝ)/1000000000000 := rfl
    have hx : (point 180+point 181)/2 = (1599547:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_180
  · change upperValue ((point (181)+point ((181)+1))/2) ≤ payment (181)
    have hp : payment 181 = (6026239611503:ℝ)/1000000000000 := rfl
    have hx : (point 181+point 182)/2 = (533867:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_181
  · change upperValue ((point (182)+point ((182)+1))/2) ≤ payment (182)
    have hp : payment 182 = (6016862625831:ℝ)/1000000000000 := rfl
    have hx : (point 182+point 183)/2 = (1603655:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_182
  · change upperValue ((point (183)+point ((183)+1))/2) ≤ payment (183)
    have hp : payment 183 = (6007508613749:ℝ)/1000000000000 := rfl
    have hx : (point 183+point 184)/2 = (1605709:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_183
  · change upperValue ((point (184)+point ((184)+1))/2) ≤ payment (184)
    have hp : payment 184 = (5998177486536:ℝ)/1000000000000 := rfl
    have hx : (point 184+point 185)/2 = (535921:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_184
  · change upperValue ((point (185)+point ((185)+1))/2) ≤ payment (185)
    have hp : payment 185 = (5988869155923:ℝ)/1000000000000 := rfl
    have hx : (point 185+point 186)/2 = (1609817:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_185
  · change upperValue ((point (186)+point ((186)+1))/2) ≤ payment (186)
    have hp : payment 186 = (5979583534094:ℝ)/1000000000000 := rfl
    have hx : (point 186+point 187)/2 = (1611871:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_186
  · change upperValue ((point (187)+point ((187)+1))/2) ≤ payment (187)
    have hp : payment 187 = (5970320533673:ℝ)/1000000000000 := rfl
    have hx : (point 187+point 188)/2 = (537975:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_187
  · change upperValue ((point (188)+point ((188)+1))/2) ≤ payment (188)
    have hp : payment 188 = (5961080067735:ℝ)/1000000000000 := rfl
    have hx : (point 188+point 189)/2 = (1615979:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_188
  · change upperValue ((point (189)+point ((189)+1))/2) ≤ payment (189)
    have hp : payment 189 = (5951862049790:ℝ)/1000000000000 := rfl
    have hx : (point 189+point 190)/2 = (1618033:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_189
  · change upperValue ((point (190)+point ((190)+1))/2) ≤ payment (190)
    have hp : payment 190 = (5942666393789:ℝ)/1000000000000 := rfl
    have hx : (point 190+point 191)/2 = (540029:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_190
  · change upperValue ((point (191)+point ((191)+1))/2) ≤ payment (191)
    have hp : payment 191 = (5933493014118:ℝ)/1000000000000 := rfl
    have hx : (point 191+point 192)/2 = (1622141:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_191
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_011
