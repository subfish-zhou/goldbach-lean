import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints012
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_012 (j : Fin 16) : upperValue ((point (16*12+j.val)+point ((16*12+j.val)+1))/2) ≤ payment (16*12+j.val) := by
  fin_cases j
  · change upperValue ((point (192)+point ((192)+1))/2) ≤ payment (192)
    have hp : payment 192 = (5924341825595:ℝ)/1000000000000 := rfl
    have hx : (point 192+point 193)/2 = (1624195:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_192
  · change upperValue ((point (193)+point ((193)+1))/2) ≤ payment (193)
    have hp : payment 193 = (5915212743468:ℝ)/1000000000000 := rfl
    have hx : (point 193+point 194)/2 = (542083:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_193
  · change upperValue ((point (194)+point ((194)+1))/2) ≤ payment (194)
    have hp : payment 194 = (5906105683411:ℝ)/1000000000000 := rfl
    have hx : (point 194+point 195)/2 = (1628303:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_194
  · change upperValue ((point (195)+point ((195)+1))/2) ≤ payment (195)
    have hp : payment 195 = (5897020561526:ℝ)/1000000000000 := rfl
    have hx : (point 195+point 196)/2 = (1630357:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_195
  · change upperValue ((point (196)+point ((196)+1))/2) ≤ payment (196)
    have hp : payment 196 = (5887957294332:ℝ)/1000000000000 := rfl
    have hx : (point 196+point 197)/2 = (544137:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_196
  · change upperValue ((point (197)+point ((197)+1))/2) ≤ payment (197)
    have hp : payment 197 = (5878915798771:ℝ)/1000000000000 := rfl
    have hx : (point 197+point 198)/2 = (1634465:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_197
  · change upperValue ((point (198)+point ((198)+1))/2) ≤ payment (198)
    have hp : payment 198 = (5869895992199:ℝ)/1000000000000 := rfl
    have hx : (point 198+point 199)/2 = (1636519:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_198
  · change upperValue ((point (199)+point ((199)+1))/2) ≤ payment (199)
    have hp : payment 199 = (5860897792386:ℝ)/1000000000000 := rfl
    have hx : (point 199+point 200)/2 = (546191:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_199
  · change upperValue ((point (200)+point ((200)+1))/2) ≤ payment (200)
    have hp : payment 200 = (5851921117515:ℝ)/1000000000000 := rfl
    have hx : (point 200+point 201)/2 = (1640627:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_200
  · change upperValue ((point (201)+point ((201)+1))/2) ≤ payment (201)
    have hp : payment 201 = (5842965886177:ℝ)/1000000000000 := rfl
    have hx : (point 201+point 202)/2 = (1642681:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_201
  · change upperValue ((point (202)+point ((202)+1))/2) ≤ payment (202)
    have hp : payment 202 = (5834032017367:ℝ)/1000000000000 := rfl
    have hx : (point 202+point 203)/2 = (548245:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_202
  · change upperValue ((point (203)+point ((203)+1))/2) ≤ payment (203)
    have hp : payment 203 = (5825119430487:ℝ)/1000000000000 := rfl
    have hx : (point 203+point 204)/2 = (1646789:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_203
  · change upperValue ((point (204)+point ((204)+1))/2) ≤ payment (204)
    have hp : payment 204 = (5816228045337:ℝ)/1000000000000 := rfl
    have hx : (point 204+point 205)/2 = (1648843:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_204
  · change upperValue ((point (205)+point ((205)+1))/2) ≤ payment (205)
    have hp : payment 205 = (5807357782119:ℝ)/1000000000000 := rfl
    have hx : (point 205+point 206)/2 = (550299:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_205
  · change upperValue ((point (206)+point ((206)+1))/2) ≤ payment (206)
    have hp : payment 206 = (5798508561427:ℝ)/1000000000000 := rfl
    have hx : (point 206+point 207)/2 = (1652951:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_206
  · change upperValue ((point (207)+point ((207)+1))/2) ≤ payment (207)
    have hp : payment 207 = (5789680304252:ℝ)/1000000000000 := rfl
    have hx : (point 207+point 208)/2 = (1655005:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_207
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_012
