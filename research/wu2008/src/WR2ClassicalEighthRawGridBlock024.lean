import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints024
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_024 (j : Fin 16) : upperValue ((point (16*24+j.val)+point ((16*24+j.val)+1))/2) ≤ payment (16*24+j.val) := by
  fin_cases j
  · change upperValue ((point (384)+point ((384)+1))/2) ≤ payment (384)
    have hp : payment 384 = (4496636070897:ℝ)/1000000000000 := rfl
    have hx : (point 384+point 385)/2 = (2018563:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_384
  · change upperValue ((point (385)+point ((385)+1))/2) ≤ payment (385)
    have hp : payment 385 = (4490573445060:ℝ)/1000000000000 := rfl
    have hx : (point 385+point 386)/2 = (673539:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_385
  · change upperValue ((point (386)+point ((386)+1))/2) ≤ payment (386)
    have hp : payment 386 = (4484522207971:ℝ)/1000000000000 := rfl
    have hx : (point 386+point 387)/2 = (2022671:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_386
  · change upperValue ((point (387)+point ((387)+1))/2) ≤ payment (387)
    have hp : payment 387 = (4478482324341:ℝ)/1000000000000 := rfl
    have hx : (point 387+point 388)/2 = (2024725:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_387
  · change upperValue ((point (388)+point ((388)+1))/2) ≤ payment (388)
    have hp : payment 388 = (4472453759025:ℝ)/1000000000000 := rfl
    have hx : (point 388+point 389)/2 = (675593:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_388
  · change upperValue ((point (389)+point ((389)+1))/2) ≤ payment (389)
    have hp : payment 389 = (4466436477019:ℝ)/1000000000000 := rfl
    have hx : (point 389+point 390)/2 = (2028833:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_389
  · change upperValue ((point (390)+point ((390)+1))/2) ≤ payment (390)
    have hp : payment 390 = (4460430443458:ℝ)/1000000000000 := rfl
    have hx : (point 390+point 391)/2 = (2030887:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_390
  · change upperValue ((point (391)+point ((391)+1))/2) ≤ payment (391)
    have hp : payment 391 = (4454435623621:ℝ)/1000000000000 := rfl
    have hx : (point 391+point 392)/2 = (677647:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_391
  · change upperValue ((point (392)+point ((392)+1))/2) ≤ payment (392)
    have hp : payment 392 = (4448451982924:ℝ)/1000000000000 := rfl
    have hx : (point 392+point 393)/2 = (2034995:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_392
  · change upperValue ((point (393)+point ((393)+1))/2) ≤ payment (393)
    have hp : payment 393 = (4442479486922:ℝ)/1000000000000 := rfl
    have hx : (point 393+point 394)/2 = (2037049:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_393
  · change upperValue ((point (394)+point ((394)+1))/2) ≤ payment (394)
    have hp : payment 394 = (4436518101311:ℝ)/1000000000000 := rfl
    have hx : (point 394+point 395)/2 = (679701:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_394
  · change upperValue ((point (395)+point ((395)+1))/2) ≤ payment (395)
    have hp : payment 395 = (4430567791921:ℝ)/1000000000000 := rfl
    have hx : (point 395+point 396)/2 = (2041157:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_395
  · change upperValue ((point (396)+point ((396)+1))/2) ≤ payment (396)
    have hp : payment 396 = (4424628524721:ℝ)/1000000000000 := rfl
    have hx : (point 396+point 397)/2 = (2043211:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_396
  · change upperValue ((point (397)+point ((397)+1))/2) ≤ payment (397)
    have hp : payment 397 = (4418700265816:ℝ)/1000000000000 := rfl
    have hx : (point 397+point 398)/2 = (681755:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_397
  · change upperValue ((point (398)+point ((398)+1))/2) ≤ payment (398)
    have hp : payment 398 = (4412782981446:ℝ)/1000000000000 := rfl
    have hx : (point 398+point 399)/2 = (2047319:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_398
  · change upperValue ((point (399)+point ((399)+1))/2) ≤ payment (399)
    have hp : payment 399 = (4406876637986:ℝ)/1000000000000 := rfl
    have hx : (point 399+point 400)/2 = (2049373:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_399
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_024
