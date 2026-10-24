import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints014
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_014 (j : Fin 16) : upperValue ((point (16*14+j.val)+point ((16*14+j.val)+1))/2) ≤ payment (16*14+j.val) := by
  fin_cases j
  · change upperValue ((point (224)+point ((224)+1))/2) ≤ payment (224)
    have hp : payment 224 = (5642732647989:ℝ)/1000000000000 := rfl
    have hx : (point 224+point 225)/2 = (1689923:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_224
  · change upperValue ((point (225)+point ((225)+1))/2) ≤ payment (225)
    have hp : payment 225 = (5634268657888:ℝ)/1000000000000 := rfl
    have hx : (point 225+point 226)/2 = (1691977:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_225
  · change upperValue ((point (226)+point ((226)+1))/2) ≤ payment (226)
    have hp : payment 226 = (5625824201763:ℝ)/1000000000000 := rfl
    have hx : (point 226+point 227)/2 = (564677:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_226
  · change upperValue ((point (227)+point ((227)+1))/2) ≤ payment (227)
    have hp : payment 227 = (5617399207988:ℝ)/1000000000000 := rfl
    have hx : (point 227+point 228)/2 = (1696085:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_227
  · change upperValue ((point (228)+point ((228)+1))/2) ≤ payment (228)
    have hp : payment 228 = (5608993605283:ℝ)/1000000000000 := rfl
    have hx : (point 228+point 229)/2 = (1698139:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_228
  · change upperValue ((point (229)+point ((229)+1))/2) ≤ payment (229)
    have hp : payment 229 = (5600607322711:ℝ)/1000000000000 := rfl
    have hx : (point 229+point 230)/2 = (566731:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_229
  · change upperValue ((point (230)+point ((230)+1))/2) ≤ payment (230)
    have hp : payment 230 = (5592240289678:ℝ)/1000000000000 := rfl
    have hx : (point 230+point 231)/2 = (1702247:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_230
  · change upperValue ((point (231)+point ((231)+1))/2) ≤ payment (231)
    have hp : payment 231 = (5583892435929:ℝ)/1000000000000 := rfl
    have hx : (point 231+point 232)/2 = (1704301:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_231
  · change upperValue ((point (232)+point ((232)+1))/2) ≤ payment (232)
    have hp : payment 232 = (5575563691546:ℝ)/1000000000000 := rfl
    have hx : (point 232+point 233)/2 = (568785:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_232
  · change upperValue ((point (233)+point ((233)+1))/2) ≤ payment (233)
    have hp : payment 233 = (5567253986948:ℝ)/1000000000000 := rfl
    have hx : (point 233+point 234)/2 = (1708409:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_233
  · change upperValue ((point (234)+point ((234)+1))/2) ≤ payment (234)
    have hp : payment 234 = (5558963252889:ℝ)/1000000000000 := rfl
    have hx : (point 234+point 235)/2 = (1710463:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_234
  · change upperValue ((point (235)+point ((235)+1))/2) ≤ payment (235)
    have hp : payment 235 = (5550691420451:ℝ)/1000000000000 := rfl
    have hx : (point 235+point 236)/2 = (570839:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_235
  · change upperValue ((point (236)+point ((236)+1))/2) ≤ payment (236)
    have hp : payment 236 = (5542438421048:ℝ)/1000000000000 := rfl
    have hx : (point 236+point 237)/2 = (1714571:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_236
  · change upperValue ((point (237)+point ((237)+1))/2) ≤ payment (237)
    have hp : payment 237 = (5534204186422:ℝ)/1000000000000 := rfl
    have hx : (point 237+point 238)/2 = (1716625:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_237
  · change upperValue ((point (238)+point ((238)+1))/2) ≤ payment (238)
    have hp : payment 238 = (5525988648640:ℝ)/1000000000000 := rfl
    have hx : (point 238+point 239)/2 = (572893:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_238
  · change upperValue ((point (239)+point ((239)+1))/2) ≤ payment (239)
    have hp : payment 239 = (5517791740093:ℝ)/1000000000000 := rfl
    have hx : (point 239+point 240)/2 = (1720733:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_239
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_014
