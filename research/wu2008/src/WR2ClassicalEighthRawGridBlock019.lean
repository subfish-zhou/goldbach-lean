import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints019
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_019 (j : Fin 16) : upperValue ((point (16*19+j.val)+point ((16*19+j.val)+1))/2) ≤ payment (16*19+j.val) := by
  fin_cases j
  · change upperValue ((point (304)+point ((304)+1))/2) ≤ payment (304)
    have hp : payment 304 = (5021957146545:ℝ)/1000000000000 := rfl
    have hx : (point 304+point 305)/2 = (618081:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_304
  · change upperValue ((point (305)+point ((305)+1))/2) ≤ payment (305)
    have hp : payment 305 = (5014854986229:ℝ)/1000000000000 := rfl
    have hx : (point 305+point 306)/2 = (1856297:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_305
  · change upperValue ((point (306)+point ((306)+1))/2) ≤ payment (306)
    have hp : payment 306 = (5007767572617:ℝ)/1000000000000 := rfl
    have hx : (point 306+point 307)/2 = (1858351:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_306
  · change upperValue ((point (307)+point ((307)+1))/2) ≤ payment (307)
    have hp : payment 307 = (5000694856225:ℝ)/1000000000000 := rfl
    have hx : (point 307+point 308)/2 = (620135:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_307
  · change upperValue ((point (308)+point ((308)+1))/2) ≤ payment (308)
    have hp : payment 308 = (4993636787787:ℝ)/1000000000000 := rfl
    have hx : (point 308+point 309)/2 = (1862459:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_308
  · change upperValue ((point (309)+point ((309)+1))/2) ≤ payment (309)
    have hp : payment 309 = (4986593318253:ℝ)/1000000000000 := rfl
    have hx : (point 309+point 310)/2 = (1864513:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_309
  · change upperValue ((point (310)+point ((310)+1))/2) ≤ payment (310)
    have hp : payment 310 = (4979564398789:ℝ)/1000000000000 := rfl
    have hx : (point 310+point 311)/2 = (622189:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_310
  · change upperValue ((point (311)+point ((311)+1))/2) ≤ payment (311)
    have hp : payment 311 = (4972549980775:ℝ)/1000000000000 := rfl
    have hx : (point 311+point 312)/2 = (1868621:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_311
  · change upperValue ((point (312)+point ((312)+1))/2) ≤ payment (312)
    have hp : payment 312 = (4965550015803:ℝ)/1000000000000 := rfl
    have hx : (point 312+point 313)/2 = (1870675:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_312
  · change upperValue ((point (313)+point ((313)+1))/2) ≤ payment (313)
    have hp : payment 313 = (4958564455679:ℝ)/1000000000000 := rfl
    have hx : (point 313+point 314)/2 = (624243:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_313
  · change upperValue ((point (314)+point ((314)+1))/2) ≤ payment (314)
    have hp : payment 314 = (4951593252418:ℝ)/1000000000000 := rfl
    have hx : (point 314+point 315)/2 = (1874783:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_314
  · change upperValue ((point (315)+point ((315)+1))/2) ≤ payment (315)
    have hp : payment 315 = (4944636358244:ℝ)/1000000000000 := rfl
    have hx : (point 315+point 316)/2 = (1876837:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_315
  · change upperValue ((point (316)+point ((316)+1))/2) ≤ payment (316)
    have hp : payment 316 = (4937693725592:ℝ)/1000000000000 := rfl
    have hx : (point 316+point 317)/2 = (626297:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_316
  · change upperValue ((point (317)+point ((317)+1))/2) ≤ payment (317)
    have hp : payment 317 = (4930765307102:ℝ)/1000000000000 := rfl
    have hx : (point 317+point 318)/2 = (1880945:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_317
  · change upperValue ((point (318)+point ((318)+1))/2) ≤ payment (318)
    have hp : payment 318 = (4923851055620:ℝ)/1000000000000 := rfl
    have hx : (point 318+point 319)/2 = (1882999:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_318
  · change upperValue ((point (319)+point ((319)+1))/2) ≤ payment (319)
    have hp : payment 319 = (4916950924198:ℝ)/1000000000000 := rfl
    have hx : (point 319+point 320)/2 = (628351:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_319
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_019
