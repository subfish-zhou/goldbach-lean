import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints013
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_013 (j : Fin 16) : upperValue ((point (16*13+j.val)+point ((16*13+j.val)+1))/2) ≤ payment (16*13+j.val) := by
  fin_cases j
  · change upperValue ((point (208)+point ((208)+1))/2) ≤ payment (208)
    have hp : payment 208 = (5780872931975:ℝ)/1000000000000 := rfl
    have hx : (point 208+point 209)/2 = (552353:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_208
  · change upperValue ((point (209)+point ((209)+1))/2) ≤ payment (209)
    have hp : payment 209 = (5772086366365:ℝ)/1000000000000 := rfl
    have hx : (point 209+point 210)/2 = (1659113:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_209
  · change upperValue ((point (210)+point ((210)+1))/2) ≤ payment (210)
    have hp : payment 210 = (5763320529579:ℝ)/1000000000000 := rfl
    have hx : (point 210+point 211)/2 = (1661167:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_210
  · change upperValue ((point (211)+point ((211)+1))/2) ≤ payment (211)
    have hp : payment 211 = (5754575344156:ℝ)/1000000000000 := rfl
    have hx : (point 211+point 212)/2 = (554407:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_211
  · change upperValue ((point (212)+point ((212)+1))/2) ≤ payment (212)
    have hp : payment 212 = (5745850733020:ℝ)/1000000000000 := rfl
    have hx : (point 212+point 213)/2 = (1665275:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_212
  · change upperValue ((point (213)+point ((213)+1))/2) ≤ payment (213)
    have hp : payment 213 = (5737146619469:ℝ)/1000000000000 := rfl
    have hx : (point 213+point 214)/2 = (1667329:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_213
  · change upperValue ((point (214)+point ((214)+1))/2) ≤ payment (214)
    have hp : payment 214 = (5728462927184:ℝ)/1000000000000 := rfl
    have hx : (point 214+point 215)/2 = (556461:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_214
  · change upperValue ((point (215)+point ((215)+1))/2) ≤ payment (215)
    have hp : payment 215 = (5719799580216:ℝ)/1000000000000 := rfl
    have hx : (point 215+point 216)/2 = (1671437:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_215
  · change upperValue ((point (216)+point ((216)+1))/2) ≤ payment (216)
    have hp : payment 216 = (5711156502991:ℝ)/1000000000000 := rfl
    have hx : (point 216+point 217)/2 = (1673491:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_216
  · change upperValue ((point (217)+point ((217)+1))/2) ≤ payment (217)
    have hp : payment 217 = (5702533620303:ℝ)/1000000000000 := rfl
    have hx : (point 217+point 218)/2 = (558515:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_217
  · change upperValue ((point (218)+point ((218)+1))/2) ≤ payment (218)
    have hp : payment 218 = (5693930857315:ℝ)/1000000000000 := rfl
    have hx : (point 218+point 219)/2 = (1677599:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_218
  · change upperValue ((point (219)+point ((219)+1))/2) ≤ payment (219)
    have hp : payment 219 = (5685348139556:ℝ)/1000000000000 := rfl
    have hx : (point 219+point 220)/2 = (1679653:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_219
  · change upperValue ((point (220)+point ((220)+1))/2) ≤ payment (220)
    have hp : payment 220 = (5676785392917:ℝ)/1000000000000 := rfl
    have hx : (point 220+point 221)/2 = (560569:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_220
  · change upperValue ((point (221)+point ((221)+1))/2) ≤ payment (221)
    have hp : payment 221 = (5668242543651:ℝ)/1000000000000 := rfl
    have hx : (point 221+point 222)/2 = (1683761:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_221
  · change upperValue ((point (222)+point ((222)+1))/2) ≤ payment (222)
    have hp : payment 222 = (5659719518370:ℝ)/1000000000000 := rfl
    have hx : (point 222+point 223)/2 = (1685815:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_222
  · change upperValue ((point (223)+point ((223)+1))/2) ≤ payment (223)
    have hp : payment 223 = (5651216244042:ℝ)/1000000000000 := rfl
    have hx : (point 223+point 224)/2 = (562623:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_223
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_013
