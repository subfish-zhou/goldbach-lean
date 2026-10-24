import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints022
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_022 (j : Fin 16) : upperValue ((point (16*22+j.val)+point ((16*22+j.val)+1))/2) ≤ payment (16*22+j.val) := by
  fin_cases j
  · change upperValue ((point (352)+point ((352)+1))/2) ≤ payment (352)
    have hp : payment 352 = (4696872269607:ℝ)/1000000000000 := rfl
    have hx : (point 352+point 353)/2 = (650945:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_352
  · change upperValue ((point (353)+point ((353)+1))/2) ≤ payment (353)
    have hp : payment 353 = (4690425678999:ℝ)/1000000000000 := rfl
    have hx : (point 353+point 354)/2 = (1954889:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_353
  · change upperValue ((point (354)+point ((354)+1))/2) ≤ payment (354)
    have hp : payment 354 = (4683991686193:ℝ)/1000000000000 := rfl
    have hx : (point 354+point 355)/2 = (1956943:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_354
  · change upperValue ((point (355)+point ((355)+1))/2) ≤ payment (355)
    have hp : payment 355 = (4677570250930:ℝ)/1000000000000 := rfl
    have hx : (point 355+point 356)/2 = (652999:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_355
  · change upperValue ((point (356)+point ((356)+1))/2) ≤ payment (356)
    have hp : payment 356 = (4671161333120:ℝ)/1000000000000 := rfl
    have hx : (point 356+point 357)/2 = (1961051:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_356
  · change upperValue ((point (357)+point ((357)+1))/2) ≤ payment (357)
    have hp : payment 357 = (4664764892840:ℝ)/1000000000000 := rfl
    have hx : (point 357+point 358)/2 = (1963105:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_357
  · change upperValue ((point (358)+point ((358)+1))/2) ≤ payment (358)
    have hp : payment 358 = (4658380890333:ℝ)/1000000000000 := rfl
    have hx : (point 358+point 359)/2 = (655053:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_358
  · change upperValue ((point (359)+point ((359)+1))/2) ≤ payment (359)
    have hp : payment 359 = (4652009286006:ℝ)/1000000000000 := rfl
    have hx : (point 359+point 360)/2 = (1967213:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_359
  · change upperValue ((point (360)+point ((360)+1))/2) ≤ payment (360)
    have hp : payment 360 = (4645650040434:ℝ)/1000000000000 := rfl
    have hx : (point 360+point 361)/2 = (1969267:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_360
  · change upperValue ((point (361)+point ((361)+1))/2) ≤ payment (361)
    have hp : payment 361 = (4639303114354:ℝ)/1000000000000 := rfl
    have hx : (point 361+point 362)/2 = (657107:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_361
  · change upperValue ((point (362)+point ((362)+1))/2) ≤ payment (362)
    have hp : payment 362 = (4632968468665:ℝ)/1000000000000 := rfl
    have hx : (point 362+point 363)/2 = (1973375:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_362
  · change upperValue ((point (363)+point ((363)+1))/2) ≤ payment (363)
    have hp : payment 363 = (4626646064430:ℝ)/1000000000000 := rfl
    have hx : (point 363+point 364)/2 = (1975429:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_363
  · change upperValue ((point (364)+point ((364)+1))/2) ≤ payment (364)
    have hp : payment 364 = (4620335862872:ℝ)/1000000000000 := rfl
    have hx : (point 364+point 365)/2 = (659161:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_364
  · change upperValue ((point (365)+point ((365)+1))/2) ≤ payment (365)
    have hp : payment 365 = (4614037825375:ℝ)/1000000000000 := rfl
    have hx : (point 365+point 366)/2 = (1979537:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_365
  · change upperValue ((point (366)+point ((366)+1))/2) ≤ payment (366)
    have hp : payment 366 = (4607751913482:ℝ)/1000000000000 := rfl
    have hx : (point 366+point 367)/2 = (1981591:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_366
  · change upperValue ((point (367)+point ((367)+1))/2) ≤ payment (367)
    have hp : payment 367 = (4601478088895:ℝ)/1000000000000 := rfl
    have hx : (point 367+point 368)/2 = (661215:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_367
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_022
