import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints026
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_026 (j : Fin 16) : upperValue ((point (16*26+j.val)+point ((16*26+j.val)+1))/2) ≤ payment (16*26+j.val) := by
  fin_cases j
  · change upperValue ((point (416)+point ((416)+1))/2) ≤ payment (416)
    have hp : payment 416 = (4308110815455:ℝ)/1000000000000 := rfl
    have hx : (point 416+point 417)/2 = (2084291:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_416
  · change upperValue ((point (417)+point ((417)+1))/2) ≤ payment (417)
    have hp : payment 417 = (4302395808236:ℝ)/1000000000000 := rfl
    have hx : (point 417+point 418)/2 = (2086345:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_417
  · change upperValue ((point (418)+point ((418)+1))/2) ≤ payment (418)
    have hp : payment 418 = (4296691127795:ℝ)/1000000000000 := rfl
    have hx : (point 418+point 419)/2 = (696133:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_418
  · change upperValue ((point (419)+point ((419)+1))/2) ≤ payment (419)
    have hp : payment 419 = (4290996743065:ℝ)/1000000000000 := rfl
    have hx : (point 419+point 420)/2 = (2090453:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_419
  · change upperValue ((point (420)+point ((420)+1))/2) ≤ payment (420)
    have hp : payment 420 = (4285312623102:ℝ)/1000000000000 := rfl
    have hx : (point 420+point 421)/2 = (2092507:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_420
  · change upperValue ((point (421)+point ((421)+1))/2) ≤ payment (421)
    have hp : payment 421 = (4279638737085:ℝ)/1000000000000 := rfl
    have hx : (point 421+point 422)/2 = (698187:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_421
  · change upperValue ((point (422)+point ((422)+1))/2) ≤ payment (422)
    have hp : payment 422 = (4273975054311:ℝ)/1000000000000 := rfl
    have hx : (point 422+point 423)/2 = (2096615:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_422
  · change upperValue ((point (423)+point ((423)+1))/2) ≤ payment (423)
    have hp : payment 423 = (4268321544196:ℝ)/1000000000000 := rfl
    have hx : (point 423+point 424)/2 = (2098669:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_423
  · change upperValue ((point (424)+point ((424)+1))/2) ≤ payment (424)
    have hp : payment 424 = (4262678176276:ℝ)/1000000000000 := rfl
    have hx : (point 424+point 425)/2 = (700241:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_424
  · change upperValue ((point (425)+point ((425)+1))/2) ≤ payment (425)
    have hp : payment 425 = (4257044920207:ℝ)/1000000000000 := rfl
    have hx : (point 425+point 426)/2 = (2102777:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_425
  · change upperValue ((point (426)+point ((426)+1))/2) ≤ payment (426)
    have hp : payment 426 = (4251421745762:ℝ)/1000000000000 := rfl
    have hx : (point 426+point 427)/2 = (2104831:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_426
  · change upperValue ((point (427)+point ((427)+1))/2) ≤ payment (427)
    have hp : payment 427 = (4245808622829:ℝ)/1000000000000 := rfl
    have hx : (point 427+point 428)/2 = (702295:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_427
  · change upperValue ((point (428)+point ((428)+1))/2) ≤ payment (428)
    have hp : payment 428 = (4240205521416:ℝ)/1000000000000 := rfl
    have hx : (point 428+point 429)/2 = (2108939:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_428
  · change upperValue ((point (429)+point ((429)+1))/2) ≤ payment (429)
    have hp : payment 429 = (4234612411645:ℝ)/1000000000000 := rfl
    have hx : (point 429+point 430)/2 = (2110993:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_429
  · change upperValue ((point (430)+point ((430)+1))/2) ≤ payment (430)
    have hp : payment 430 = (4229029263756:ℝ)/1000000000000 := rfl
    have hx : (point 430+point 431)/2 = (704349:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_430
  · change upperValue ((point (431)+point ((431)+1))/2) ≤ payment (431)
    have hp : payment 431 = (4223456048102:ℝ)/1000000000000 := rfl
    have hx : (point 431+point 432)/2 = (2115101:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_431
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_026
