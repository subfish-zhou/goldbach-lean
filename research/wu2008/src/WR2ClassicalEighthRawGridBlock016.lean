import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints016
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_016 (j : Fin 16) : upperValue ((point (16*16+j.val)+point ((16*16+j.val)+1))/2) ≤ payment (16*16+j.val) := by
  fin_cases j
  · change upperValue ((point (256)+point ((256)+1))/2) ≤ payment (256)
    have hp : payment 256 = (5381230585095:ℝ)/1000000000000 := rfl
    have hx : (point 256+point 257)/2 = (585217:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_256
  · change upperValue ((point (257)+point ((257)+1))/2) ≤ payment (257)
    have hp : payment 257 = (5373357799534:ℝ)/1000000000000 := rfl
    have hx : (point 257+point 258)/2 = (1757705:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_257
  · change upperValue ((point (258)+point ((258)+1))/2) ≤ payment (258)
    have hp : payment 258 = (5365502417677:ℝ)/1000000000000 := rfl
    have hx : (point 258+point 259)/2 = (1759759:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_258
  · change upperValue ((point (259)+point ((259)+1))/2) ≤ payment (259)
    have hp : payment 259 = (5357664378006:ℝ)/1000000000000 := rfl
    have hx : (point 259+point 260)/2 = (587271:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_259
  · change upperValue ((point (260)+point ((260)+1))/2) ≤ payment (260)
    have hp : payment 260 = (5349843619284:ℝ)/1000000000000 := rfl
    have hx : (point 260+point 261)/2 = (1763867:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_260
  · change upperValue ((point (261)+point ((261)+1))/2) ≤ payment (261)
    have hp : payment 261 = (5342040080564:ℝ)/1000000000000 := rfl
    have hx : (point 261+point 262)/2 = (1765921:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_261
  · change upperValue ((point (262)+point ((262)+1))/2) ≤ payment (262)
    have hp : payment 262 = (5334253701177:ℝ)/1000000000000 := rfl
    have hx : (point 262+point 263)/2 = (589325:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_262
  · change upperValue ((point (263)+point ((263)+1))/2) ≤ payment (263)
    have hp : payment 263 = (5326484420738:ℝ)/1000000000000 := rfl
    have hx : (point 263+point 264)/2 = (1770029:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_263
  · change upperValue ((point (264)+point ((264)+1))/2) ≤ payment (264)
    have hp : payment 264 = (5318732179140:ℝ)/1000000000000 := rfl
    have hx : (point 264+point 265)/2 = (1772083:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_264
  · change upperValue ((point (265)+point ((265)+1))/2) ≤ payment (265)
    have hp : payment 265 = (5310996916554:ℝ)/1000000000000 := rfl
    have hx : (point 265+point 266)/2 = (591379:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_265
  · change upperValue ((point (266)+point ((266)+1))/2) ≤ payment (266)
    have hp : payment 266 = (5303278573429:ℝ)/1000000000000 := rfl
    have hx : (point 266+point 267)/2 = (1776191:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_266
  · change upperValue ((point (267)+point ((267)+1))/2) ≤ payment (267)
    have hp : payment 267 = (5295577090485:ℝ)/1000000000000 := rfl
    have hx : (point 267+point 268)/2 = (1778245:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_267
  · change upperValue ((point (268)+point ((268)+1))/2) ≤ payment (268)
    have hp : payment 268 = (5287892408719:ℝ)/1000000000000 := rfl
    have hx : (point 268+point 269)/2 = (593433:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_268
  · change upperValue ((point (269)+point ((269)+1))/2) ≤ payment (269)
    have hp : payment 269 = (5280224469396:ℝ)/1000000000000 := rfl
    have hx : (point 269+point 270)/2 = (1782353:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_269
  · change upperValue ((point (270)+point ((270)+1))/2) ≤ payment (270)
    have hp : payment 270 = (5272573214054:ℝ)/1000000000000 := rfl
    have hx : (point 270+point 271)/2 = (1784407:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_270
  · change upperValue ((point (271)+point ((271)+1))/2) ≤ payment (271)
    have hp : payment 271 = (5264938584497:ℝ)/1000000000000 := rfl
    have hx : (point 271+point 272)/2 = (595487:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_271
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_016
