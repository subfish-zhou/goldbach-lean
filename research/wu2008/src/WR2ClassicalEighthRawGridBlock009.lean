import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints009
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_009 (j : Fin 16) : upperValue ((point (16*9+j.val)+point ((16*9+j.val)+1))/2) ≤ payment (16*9+j.val) := by
  fin_cases j
  · change upperValue ((point (144)+point ((144)+1))/2) ≤ payment (144)
    have hp : payment 144 = (6390192945128:ℝ)/1000000000000 := rfl
    have hx : (point 144+point 145)/2 = (1525603:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_144
  · change upperValue ((point (145)+point ((145)+1))/2) ≤ payment (145)
    have hp : payment 145 = (6379899151963:ℝ)/1000000000000 := rfl
    have hx : (point 145+point 146)/2 = (509219:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_145
  · change upperValue ((point (146)+point ((146)+1))/2) ≤ payment (146)
    have hp : payment 146 = (6369631961494:ℝ)/1000000000000 := rfl
    have hx : (point 146+point 147)/2 = (1529711:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_146
  · change upperValue ((point (147)+point ((147)+1))/2) ≤ payment (147)
    have hp : payment 147 = (6359391266019:ℝ)/1000000000000 := rfl
    have hx : (point 147+point 148)/2 = (1531765:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_147
  · change upperValue ((point (148)+point ((148)+1))/2) ≤ payment (148)
    have hp : payment 148 = (6349176958414:ℝ)/1000000000000 := rfl
    have hx : (point 148+point 149)/2 = (511273:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_148
  · change upperValue ((point (149)+point ((149)+1))/2) ≤ payment (149)
    have hp : payment 149 = (6338988932126:ℝ)/1000000000000 := rfl
    have hx : (point 149+point 150)/2 = (1535873:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_149
  · change upperValue ((point (150)+point ((150)+1))/2) ≤ payment (150)
    have hp : payment 150 = (6328827081174:ℝ)/1000000000000 := rfl
    have hx : (point 150+point 151)/2 = (1537927:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_150
  · change upperValue ((point (151)+point ((151)+1))/2) ≤ payment (151)
    have hp : payment 151 = (6318691300137:ℝ)/1000000000000 := rfl
    have hx : (point 151+point 152)/2 = (513327:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_151
  · change upperValue ((point (152)+point ((152)+1))/2) ≤ payment (152)
    have hp : payment 152 = (6308581484159:ℝ)/1000000000000 := rfl
    have hx : (point 152+point 153)/2 = (1542035:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_152
  · change upperValue ((point (153)+point ((153)+1))/2) ≤ payment (153)
    have hp : payment 153 = (6298497528939:ℝ)/1000000000000 := rfl
    have hx : (point 153+point 154)/2 = (1544089:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_153
  · change upperValue ((point (154)+point ((154)+1))/2) ≤ payment (154)
    have hp : payment 154 = (6288439330731:ℝ)/1000000000000 := rfl
    have hx : (point 154+point 155)/2 = (515381:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_154
  · change upperValue ((point (155)+point ((155)+1))/2) ≤ payment (155)
    have hp : payment 155 = (6278406786340:ℝ)/1000000000000 := rfl
    have hx : (point 155+point 156)/2 = (1548197:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_155
  · change upperValue ((point (156)+point ((156)+1))/2) ≤ payment (156)
    have hp : payment 156 = (6268399793115:ℝ)/1000000000000 := rfl
    have hx : (point 156+point 157)/2 = (1550251:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_156
  · change upperValue ((point (157)+point ((157)+1))/2) ≤ payment (157)
    have hp : payment 157 = (6258418248949:ℝ)/1000000000000 := rfl
    have hx : (point 157+point 158)/2 = (517435:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_157
  · change upperValue ((point (158)+point ((158)+1))/2) ≤ payment (158)
    have hp : payment 158 = (6248462052274:ℝ)/1000000000000 := rfl
    have hx : (point 158+point 159)/2 = (1554359:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_158
  · change upperValue ((point (159)+point ((159)+1))/2) ≤ payment (159)
    have hp : payment 159 = (6238531102057:ℝ)/1000000000000 := rfl
    have hx : (point 159+point 160)/2 = (1556413:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_159
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_009
