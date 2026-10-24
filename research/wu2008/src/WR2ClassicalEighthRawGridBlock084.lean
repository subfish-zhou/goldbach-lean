import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints084
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_084 (j : Fin 16) : upperValue ((point (16*84+j.val)+point ((16*84+j.val)+1))/2) ≤ payment (16*84+j.val) := by
  fin_cases j
  · change upperValue ((point (1344)+point ((1344)+1))/2) ≤ payment (1344)
    have hp : payment 1344 = (1275450154238:ℝ)/1000000000000 := rfl
    have hx : (point 1344+point 1345)/2 = (3990403:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1344
  · change upperValue ((point (1345)+point ((1345)+1))/2) ≤ payment (1345)
    have hp : payment 1345 = (1273391783492:ℝ)/1000000000000 := rfl
    have hx : (point 1345+point 1346)/2 = (1330819:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1345
  · change upperValue ((point (1346)+point ((1346)+1))/2) ≤ payment (1346)
    have hp : payment 1346 = (1271334579849:ℝ)/1000000000000 := rfl
    have hx : (point 1346+point 1347)/2 = (3994511:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1346
  · change upperValue ((point (1347)+point ((1347)+1))/2) ≤ payment (1347)
    have hp : payment 1347 = (1269278540746:ℝ)/1000000000000 := rfl
    have hx : (point 1347+point 1348)/2 = (3996565:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1347
  · change upperValue ((point (1348)+point ((1348)+1))/2) ≤ payment (1348)
    have hp : payment 1348 = (1267223663626:ℝ)/1000000000000 := rfl
    have hx : (point 1348+point 1349)/2 = (1332873:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1348
  · change upperValue ((point (1349)+point ((1349)+1))/2) ≤ payment (1349)
    have hp : payment 1349 = (1265169945934:ℝ)/1000000000000 := rfl
    have hx : (point 1349+point 1350)/2 = (4000673:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1349
  · change upperValue ((point (1350)+point ((1350)+1))/2) ≤ payment (1350)
    have hp : payment 1350 = (1263117385121:ℝ)/1000000000000 := rfl
    have hx : (point 1350+point 1351)/2 = (4002727:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1350
  · change upperValue ((point (1351)+point ((1351)+1))/2) ≤ payment (1351)
    have hp : payment 1351 = (1261065978643:ℝ)/1000000000000 := rfl
    have hx : (point 1351+point 1352)/2 = (1334927:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1351
  · change upperValue ((point (1352)+point ((1352)+1))/2) ≤ payment (1352)
    have hp : payment 1352 = (1259015723960:ℝ)/1000000000000 := rfl
    have hx : (point 1352+point 1353)/2 = (4006835:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1352
  · change upperValue ((point (1353)+point ((1353)+1))/2) ≤ payment (1353)
    have hp : payment 1353 = (1256966618535:ℝ)/1000000000000 := rfl
    have hx : (point 1353+point 1354)/2 = (4008889:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1353
  · change upperValue ((point (1354)+point ((1354)+1))/2) ≤ payment (1354)
    have hp : payment 1354 = (1254918659837:ℝ)/1000000000000 := rfl
    have hx : (point 1354+point 1355)/2 = (1336981:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1354
  · change upperValue ((point (1355)+point ((1355)+1))/2) ≤ payment (1355)
    have hp : payment 1355 = (1252871845340:ℝ)/1000000000000 := rfl
    have hx : (point 1355+point 1356)/2 = (4012997:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1355
  · change upperValue ((point (1356)+point ((1356)+1))/2) ≤ payment (1356)
    have hp : payment 1356 = (1250826172520:ℝ)/1000000000000 := rfl
    have hx : (point 1356+point 1357)/2 = (4015051:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1356
  · change upperValue ((point (1357)+point ((1357)+1))/2) ≤ payment (1357)
    have hp : payment 1357 = (1248781638860:ℝ)/1000000000000 := rfl
    have hx : (point 1357+point 1358)/2 = (1339035:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1357
  · change upperValue ((point (1358)+point ((1358)+1))/2) ≤ payment (1358)
    have hp : payment 1358 = (1246738241845:ℝ)/1000000000000 := rfl
    have hx : (point 1358+point 1359)/2 = (4019159:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1358
  · change upperValue ((point (1359)+point ((1359)+1))/2) ≤ payment (1359)
    have hp : payment 1359 = (1244695978966:ℝ)/1000000000000 := rfl
    have hx : (point 1359+point 1360)/2 = (4021213:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1359
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_084
