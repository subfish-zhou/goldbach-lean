import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints021
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_021 (j : Fin 16) : upperValue ((point (16*21+j.val)+point ((16*21+j.val)+1))/2) ≤ payment (16*21+j.val) := by
  fin_cases j
  · change upperValue ((point (336)+point ((336)+1))/2) ≤ payment (336)
    have hp : payment 336 = (4801764537233:ℝ)/1000000000000 := rfl
    have hx : (point 336+point 337)/2 = (1919971:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_336
  · change upperValue ((point (337)+point ((337)+1))/2) ≤ payment (337)
    have hp : payment 337 = (4795110765898:ℝ)/1000000000000 := rfl
    have hx : (point 337+point 338)/2 = (640675:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_337
  · change upperValue ((point (338)+point ((338)+1))/2) ≤ payment (338)
    have hp : payment 338 = (4788470260113:ℝ)/1000000000000 := rfl
    have hx : (point 338+point 339)/2 = (1924079:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_338
  · change upperValue ((point (339)+point ((339)+1))/2) ≤ payment (339)
    have hp : payment 339 = (4781842976804:ℝ)/1000000000000 := rfl
    have hx : (point 339+point 340)/2 = (1926133:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_339
  · change upperValue ((point (340)+point ((340)+1))/2) ≤ payment (340)
    have hp : payment 340 = (4775228873081:ℝ)/1000000000000 := rfl
    have hx : (point 340+point 341)/2 = (642729:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_340
  · change upperValue ((point (341)+point ((341)+1))/2) ≤ payment (341)
    have hp : payment 341 = (4768627906235:ℝ)/1000000000000 := rfl
    have hx : (point 341+point 342)/2 = (1930241:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_341
  · change upperValue ((point (342)+point ((342)+1))/2) ≤ payment (342)
    have hp : payment 342 = (4762040033740:ℝ)/1000000000000 := rfl
    have hx : (point 342+point 343)/2 = (1932295:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_342
  · change upperValue ((point (343)+point ((343)+1))/2) ≤ payment (343)
    have hp : payment 343 = (4755465213248:ℝ)/1000000000000 := rfl
    have hx : (point 343+point 344)/2 = (644783:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_343
  · change upperValue ((point (344)+point ((344)+1))/2) ≤ payment (344)
    have hp : payment 344 = (4748903402591:ℝ)/1000000000000 := rfl
    have hx : (point 344+point 345)/2 = (1936403:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_344
  · change upperValue ((point (345)+point ((345)+1))/2) ≤ payment (345)
    have hp : payment 345 = (4742354559779:ℝ)/1000000000000 := rfl
    have hx : (point 345+point 346)/2 = (1938457:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_345
  · change upperValue ((point (346)+point ((346)+1))/2) ≤ payment (346)
    have hp : payment 346 = (4735818643000:ℝ)/1000000000000 := rfl
    have hx : (point 346+point 347)/2 = (646837:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_346
  · change upperValue ((point (347)+point ((347)+1))/2) ≤ payment (347)
    have hp : payment 347 = (4729295610617:ℝ)/1000000000000 := rfl
    have hx : (point 347+point 348)/2 = (1942565:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_347
  · change upperValue ((point (348)+point ((348)+1))/2) ≤ payment (348)
    have hp : payment 348 = (4722785421170:ℝ)/1000000000000 := rfl
    have hx : (point 348+point 349)/2 = (1944619:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_348
  · change upperValue ((point (349)+point ((349)+1))/2) ≤ payment (349)
    have hp : payment 349 = (4716288033372:ℝ)/1000000000000 := rfl
    have hx : (point 349+point 350)/2 = (648891:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_349
  · change upperValue ((point (350)+point ((350)+1))/2) ≤ payment (350)
    have hp : payment 350 = (4709803406110:ℝ)/1000000000000 := rfl
    have hx : (point 350+point 351)/2 = (1948727:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_350
  · change upperValue ((point (351)+point ((351)+1))/2) ≤ payment (351)
    have hp : payment 351 = (4703331498445:ℝ)/1000000000000 := rfl
    have hx : (point 351+point 352)/2 = (1950781:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_351
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_021
