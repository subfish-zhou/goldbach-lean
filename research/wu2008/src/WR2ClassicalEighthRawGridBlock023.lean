import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints023
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_023 (j : Fin 16) : upperValue ((point (16*23+j.val)+point ((16*23+j.val)+1))/2) ≤ payment (16*23+j.val) := by
  fin_cases j
  · change upperValue ((point (368)+point ((368)+1))/2) ≤ payment (368)
    have hp : payment 368 = (4595216313475:ℝ)/1000000000000 := rfl
    have hx : (point 368+point 369)/2 = (1985699:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_368
  · change upperValue ((point (369)+point ((369)+1))/2) ≤ payment (369)
    have hp : payment 369 = (4588966549238:ℝ)/1000000000000 := rfl
    have hx : (point 369+point 370)/2 = (1987753:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_369
  · change upperValue ((point (370)+point ((370)+1))/2) ≤ payment (370)
    have hp : payment 370 = (4582728758358:ℝ)/1000000000000 := rfl
    have hx : (point 370+point 371)/2 = (663269:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_370
  · change upperValue ((point (371)+point ((371)+1))/2) ≤ payment (371)
    have hp : payment 371 = (4576502903164:ℝ)/1000000000000 := rfl
    have hx : (point 371+point 372)/2 = (1991861:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_371
  · change upperValue ((point (372)+point ((372)+1))/2) ≤ payment (372)
    have hp : payment 372 = (4570288946140:ℝ)/1000000000000 := rfl
    have hx : (point 372+point 373)/2 = (1993915:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_372
  · change upperValue ((point (373)+point ((373)+1))/2) ≤ payment (373)
    have hp : payment 373 = (4564086849924:ℝ)/1000000000000 := rfl
    have hx : (point 373+point 374)/2 = (665323:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_373
  · change upperValue ((point (374)+point ((374)+1))/2) ≤ payment (374)
    have hp : payment 374 = (4557896577306:ℝ)/1000000000000 := rfl
    have hx : (point 374+point 375)/2 = (1998023:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_374
  · change upperValue ((point (375)+point ((375)+1))/2) ≤ payment (375)
    have hp : payment 375 = (4551718091228:ℝ)/1000000000000 := rfl
    have hx : (point 375+point 376)/2 = (2000077:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_375
  · change upperValue ((point (376)+point ((376)+1))/2) ≤ payment (376)
    have hp : payment 376 = (4545551354787:ℝ)/1000000000000 := rfl
    have hx : (point 376+point 377)/2 = (667377:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_376
  · change upperValue ((point (377)+point ((377)+1))/2) ≤ payment (377)
    have hp : payment 377 = (4539396331227:ℝ)/1000000000000 := rfl
    have hx : (point 377+point 378)/2 = (2004185:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_377
  · change upperValue ((point (378)+point ((378)+1))/2) ≤ payment (378)
    have hp : payment 378 = (4533252983943:ℝ)/1000000000000 := rfl
    have hx : (point 378+point 379)/2 = (2006239:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_378
  · change upperValue ((point (379)+point ((379)+1))/2) ≤ payment (379)
    have hp : payment 379 = (4527121276481:ℝ)/1000000000000 := rfl
    have hx : (point 379+point 380)/2 = (669431:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_379
  · change upperValue ((point (380)+point ((380)+1))/2) ≤ payment (380)
    have hp : payment 380 = (4521001172532:ℝ)/1000000000000 := rfl
    have hx : (point 380+point 381)/2 = (2010347:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_380
  · change upperValue ((point (381)+point ((381)+1))/2) ≤ payment (381)
    have hp : payment 381 = (4514892635939:ℝ)/1000000000000 := rfl
    have hx : (point 381+point 382)/2 = (2012401:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_381
  · change upperValue ((point (382)+point ((382)+1))/2) ≤ payment (382)
    have hp : payment 382 = (4508795630689:ℝ)/1000000000000 := rfl
    have hx : (point 382+point 383)/2 = (671485:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_382
  · change upperValue ((point (383)+point ((383)+1))/2) ≤ payment (383)
    have hp : payment 383 = (4502710120915:ℝ)/1000000000000 := rfl
    have hx : (point 383+point 384)/2 = (2016509:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_383
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_023
