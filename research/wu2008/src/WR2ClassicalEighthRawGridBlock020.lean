import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints020
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_020 (j : Fin 16) : upperValue ((point (16*20+j.val)+point ((16*20+j.val)+1))/2) ≤ payment (16*20+j.val) := by
  fin_cases j
  · change upperValue ((point (320)+point ((320)+1))/2) ≤ payment (320)
    have hp : payment 320 = (4910064866092:ℝ)/1000000000000 := rfl
    have hx : (point 320+point 321)/2 = (1887107:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_320
  · change upperValue ((point (321)+point ((321)+1))/2) ≤ payment (321)
    have hp : payment 321 = (4903192834760:ℝ)/1000000000000 := rfl
    have hx : (point 321+point 322)/2 = (1889161:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_321
  · change upperValue ((point (322)+point ((322)+1))/2) ≤ payment (322)
    have hp : payment 322 = (4896334783863:ℝ)/1000000000000 := rfl
    have hx : (point 322+point 323)/2 = (630405:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_322
  · change upperValue ((point (323)+point ((323)+1))/2) ≤ payment (323)
    have hp : payment 323 = (4889490667260:ℝ)/1000000000000 := rfl
    have hx : (point 323+point 324)/2 = (1893269:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_323
  · change upperValue ((point (324)+point ((324)+1))/2) ≤ payment (324)
    have hp : payment 324 = (4882660439013:ℝ)/1000000000000 := rfl
    have hx : (point 324+point 325)/2 = (1895323:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_324
  · change upperValue ((point (325)+point ((325)+1))/2) ≤ payment (325)
    have hp : payment 325 = (4875844053378:ℝ)/1000000000000 := rfl
    have hx : (point 325+point 326)/2 = (632459:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_325
  · change upperValue ((point (326)+point ((326)+1))/2) ≤ payment (326)
    have hp : payment 326 = (4869041464813:ℝ)/1000000000000 := rfl
    have hx : (point 326+point 327)/2 = (1899431:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_326
  · change upperValue ((point (327)+point ((327)+1))/2) ≤ payment (327)
    have hp : payment 327 = (4862252627970:ℝ)/1000000000000 := rfl
    have hx : (point 327+point 328)/2 = (1901485:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_327
  · change upperValue ((point (328)+point ((328)+1))/2) ≤ payment (328)
    have hp : payment 328 = (4855477497695:ℝ)/1000000000000 := rfl
    have hx : (point 328+point 329)/2 = (634513:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_328
  · change upperValue ((point (329)+point ((329)+1))/2) ≤ payment (329)
    have hp : payment 329 = (4848716029030:ℝ)/1000000000000 := rfl
    have hx : (point 329+point 330)/2 = (1905593:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_329
  · change upperValue ((point (330)+point ((330)+1))/2) ≤ payment (330)
    have hp : payment 330 = (4841968177210:ℝ)/1000000000000 := rfl
    have hx : (point 330+point 331)/2 = (1907647:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_330
  · change upperValue ((point (331)+point ((331)+1))/2) ≤ payment (331)
    have hp : payment 331 = (4835233897661:ℝ)/1000000000000 := rfl
    have hx : (point 331+point 332)/2 = (636567:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_331
  · change upperValue ((point (332)+point ((332)+1))/2) ≤ payment (332)
    have hp : payment 332 = (4828513146001:ℝ)/1000000000000 := rfl
    have hx : (point 332+point 333)/2 = (1911755:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_332
  · change upperValue ((point (333)+point ((333)+1))/2) ≤ payment (333)
    have hp : payment 333 = (4821805878037:ℝ)/1000000000000 := rfl
    have hx : (point 333+point 334)/2 = (1913809:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_333
  · change upperValue ((point (334)+point ((334)+1))/2) ≤ payment (334)
    have hp : payment 334 = (4815112049767:ℝ)/1000000000000 := rfl
    have hx : (point 334+point 335)/2 = (638621:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_334
  · change upperValue ((point (335)+point ((335)+1))/2) ≤ payment (335)
    have hp : payment 335 = (4808431617375:ℝ)/1000000000000 := rfl
    have hx : (point 335+point 336)/2 = (1917917:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_335
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_020
