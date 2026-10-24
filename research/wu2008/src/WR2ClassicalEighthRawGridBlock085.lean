import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints085
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_085 (j : Fin 16) : upperValue ((point (16*85+j.val)+point ((16*85+j.val)+1))/2) ≤ payment (16*85+j.val) := by
  fin_cases j
  · change upperValue ((point (1360)+point ((1360)+1))/2) ≤ payment (1360)
    have hp : payment 1360 = (1242654847719:ℝ)/1000000000000 := rfl
    have hx : (point 1360+point 1361)/2 = (1341089:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1360
  · change upperValue ((point (1361)+point ((1361)+1))/2) ≤ payment (1361)
    have hp : payment 1361 = (1240614845601:ℝ)/1000000000000 := rfl
    have hx : (point 1361+point 1362)/2 = (4025321:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1361
  · change upperValue ((point (1362)+point ((1362)+1))/2) ≤ payment (1362)
    have hp : payment 1362 = (1238575970118:ℝ)/1000000000000 := rfl
    have hx : (point 1362+point 1363)/2 = (4027375:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1362
  · change upperValue ((point (1363)+point ((1363)+1))/2) ≤ payment (1363)
    have hp : payment 1363 = (1236538218776:ℝ)/1000000000000 := rfl
    have hx : (point 1363+point 1364)/2 = (1343143:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1363
  · change upperValue ((point (1364)+point ((1364)+1))/2) ≤ payment (1364)
    have hp : payment 1364 = (1234501589088:ℝ)/1000000000000 := rfl
    have hx : (point 1364+point 1365)/2 = (4031483:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1364
  · change upperValue ((point (1365)+point ((1365)+1))/2) ≤ payment (1365)
    have hp : payment 1365 = (1232466078570:ℝ)/1000000000000 := rfl
    have hx : (point 1365+point 1366)/2 = (4033537:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1365
  · change upperValue ((point (1366)+point ((1366)+1))/2) ≤ payment (1366)
    have hp : payment 1366 = (1230431684744:ℝ)/1000000000000 := rfl
    have hx : (point 1366+point 1367)/2 = (1345197:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1366
  · change upperValue ((point (1367)+point ((1367)+1))/2) ≤ payment (1367)
    have hp : payment 1367 = (1228398405133:ℝ)/1000000000000 := rfl
    have hx : (point 1367+point 1368)/2 = (4037645:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1367
  · change upperValue ((point (1368)+point ((1368)+1))/2) ≤ payment (1368)
    have hp : payment 1368 = (1226366237268:ℝ)/1000000000000 := rfl
    have hx : (point 1368+point 1369)/2 = (4039699:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1368
  · change upperValue ((point (1369)+point ((1369)+1))/2) ≤ payment (1369)
    have hp : payment 1369 = (1224335178681:ℝ)/1000000000000 := rfl
    have hx : (point 1369+point 1370)/2 = (1347251:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1369
  · change upperValue ((point (1370)+point ((1370)+1))/2) ≤ payment (1370)
    have hp : payment 1370 = (1222305226911:ℝ)/1000000000000 := rfl
    have hx : (point 1370+point 1371)/2 = (4043807:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1370
  · change upperValue ((point (1371)+point ((1371)+1))/2) ≤ payment (1371)
    have hp : payment 1371 = (1220276379500:ℝ)/1000000000000 := rfl
    have hx : (point 1371+point 1372)/2 = (4045861:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1371
  · change upperValue ((point (1372)+point ((1372)+1))/2) ≤ payment (1372)
    have hp : payment 1372 = (1218248633993:ℝ)/1000000000000 := rfl
    have hx : (point 1372+point 1373)/2 = (1349305:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1372
  · change upperValue ((point (1373)+point ((1373)+1))/2) ≤ payment (1373)
    have hp : payment 1373 = (1216221987941:ℝ)/1000000000000 := rfl
    have hx : (point 1373+point 1374)/2 = (4049969:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1373
  · change upperValue ((point (1374)+point ((1374)+1))/2) ≤ payment (1374)
    have hp : payment 1374 = (1214196438899:ℝ)/1000000000000 := rfl
    have hx : (point 1374+point 1375)/2 = (4052023:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1374
  · change upperValue ((point (1375)+point ((1375)+1))/2) ≤ payment (1375)
    have hp : payment 1375 = (1212171984425:ℝ)/1000000000000 := rfl
    have hx : (point 1375+point 1376)/2 = (1351359:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1375
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_085
