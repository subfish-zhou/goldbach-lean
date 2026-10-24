import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints018
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_018 (j : Fin 16) : upperValue ((point (16*18+j.val)+point ((16*18+j.val)+1))/2) ≤ payment (16*18+j.val) := by
  fin_cases j
  · change upperValue ((point (288)+point ((288)+1))/2) ≤ payment (288)
    have hp : payment 288 = (5137638505443:ℝ)/1000000000000 := rfl
    have hx : (point 288+point 289)/2 = (1821379:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_288
  · change upperValue ((point (289)+point ((289)+1))/2) ≤ payment (289)
    have hp : payment 289 = (5130293485557:ℝ)/1000000000000 := rfl
    have hx : (point 289+point 290)/2 = (607811:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_289
  · change upperValue ((point (290)+point ((290)+1))/2) ≤ payment (290)
    have hp : payment 290 = (5122964034748:ℝ)/1000000000000 := rfl
    have hx : (point 290+point 291)/2 = (1825487:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_290
  · change upperValue ((point (291)+point ((291)+1))/2) ≤ payment (291)
    have hp : payment 291 = (5115650099875:ℝ)/1000000000000 := rfl
    have hx : (point 291+point 292)/2 = (1827541:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_291
  · change upperValue ((point (292)+point ((292)+1))/2) ≤ payment (292)
    have hp : payment 292 = (5108351628041:ℝ)/1000000000000 := rfl
    have hx : (point 292+point 293)/2 = (609865:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_292
  · change upperValue ((point (293)+point ((293)+1))/2) ≤ payment (293)
    have hp : payment 293 = (5101068566580:ℝ)/1000000000000 := rfl
    have hx : (point 293+point 294)/2 = (1831649:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_293
  · change upperValue ((point (294)+point ((294)+1))/2) ≤ payment (294)
    have hp : payment 294 = (5093800863066:ℝ)/1000000000000 := rfl
    have hx : (point 294+point 295)/2 = (1833703:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_294
  · change upperValue ((point (295)+point ((295)+1))/2) ≤ payment (295)
    have hp : payment 295 = (5086548465304:ℝ)/1000000000000 := rfl
    have hx : (point 295+point 296)/2 = (611919:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_295
  · change upperValue ((point (296)+point ((296)+1))/2) ≤ payment (296)
    have hp : payment 296 = (5079311321334:ℝ)/1000000000000 := rfl
    have hx : (point 296+point 297)/2 = (1837811:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_296
  · change upperValue ((point (297)+point ((297)+1))/2) ≤ payment (297)
    have hp : payment 297 = (5072089379425:ℝ)/1000000000000 := rfl
    have hx : (point 297+point 298)/2 = (1839865:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_297
  · change upperValue ((point (298)+point ((298)+1))/2) ≤ payment (298)
    have hp : payment 298 = (5064882588079:ℝ)/1000000000000 := rfl
    have hx : (point 298+point 299)/2 = (613973:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_298
  · change upperValue ((point (299)+point ((299)+1))/2) ≤ payment (299)
    have hp : payment 299 = (5057690896026:ℝ)/1000000000000 := rfl
    have hx : (point 299+point 300)/2 = (1843973:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_299
  · change upperValue ((point (300)+point ((300)+1))/2) ≤ payment (300)
    have hp : payment 300 = (5050514252222:ℝ)/1000000000000 := rfl
    have hx : (point 300+point 301)/2 = (1846027:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_300
  · change upperValue ((point (301)+point ((301)+1))/2) ≤ payment (301)
    have hp : payment 301 = (5043352605851:ℝ)/1000000000000 := rfl
    have hx : (point 301+point 302)/2 = (616027:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_301
  · change upperValue ((point (302)+point ((302)+1))/2) ≤ payment (302)
    have hp : payment 302 = (5036205906322:ℝ)/1000000000000 := rfl
    have hx : (point 302+point 303)/2 = (1850135:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_302
  · change upperValue ((point (303)+point ((303)+1))/2) ≤ payment (303)
    have hp : payment 303 = (5029074103269:ℝ)/1000000000000 := rfl
    have hx : (point 303+point 304)/2 = (1852189:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_303
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_018
