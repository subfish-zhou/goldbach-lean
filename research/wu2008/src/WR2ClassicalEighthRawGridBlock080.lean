import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints080
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_080 (j : Fin 16) : upperValue ((point (16*80+j.val)+point ((16*80+j.val)+1))/2) ≤ payment (16*80+j.val) := by
  fin_cases j
  · change upperValue ((point (1280)+point ((1280)+1))/2) ≤ payment (1280)
    have hp : payment 1280 = (1409734304442:ℝ)/1000000000000 := rfl
    have hx : (point 1280+point 1281)/2 = (3858947:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1280
  · change upperValue ((point (1281)+point ((1281)+1))/2) ≤ payment (1281)
    have hp : payment 1281 = (1407595693031:ℝ)/1000000000000 := rfl
    have hx : (point 1281+point 1282)/2 = (3861001:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1281
  · change upperValue ((point (1282)+point ((1282)+1))/2) ≤ payment (1282)
    have hp : payment 1282 = (1405458422688:ℝ)/1000000000000 := rfl
    have hx : (point 1282+point 1283)/2 = (1287685:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1282
  · change upperValue ((point (1283)+point ((1283)+1))/2) ≤ payment (1283)
    have hp : payment 1283 = (1403322490536:ℝ)/1000000000000 := rfl
    have hx : (point 1283+point 1284)/2 = (3865109:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1283
  · change upperValue ((point (1284)+point ((1284)+1))/2) ≤ payment (1284)
    have hp : payment 1284 = (1401187893702:ℝ)/1000000000000 := rfl
    have hx : (point 1284+point 1285)/2 = (3867163:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1284
  · change upperValue ((point (1285)+point ((1285)+1))/2) ≤ payment (1285)
    have hp : payment 1285 = (1399054629318:ℝ)/1000000000000 := rfl
    have hx : (point 1285+point 1286)/2 = (1289739:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1285
  · change upperValue ((point (1286)+point ((1286)+1))/2) ≤ payment (1286)
    have hp : payment 1286 = (1396922694521:ℝ)/1000000000000 := rfl
    have hx : (point 1286+point 1287)/2 = (3871271:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1286
  · change upperValue ((point (1287)+point ((1287)+1))/2) ≤ payment (1287)
    have hp : payment 1287 = (1394792086456:ℝ)/1000000000000 := rfl
    have hx : (point 1287+point 1288)/2 = (3873325:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1287
  · change upperValue ((point (1288)+point ((1288)+1))/2) ≤ payment (1288)
    have hp : payment 1288 = (1392662802270:ℝ)/1000000000000 := rfl
    have hx : (point 1288+point 1289)/2 = (1291793:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1288
  · change upperValue ((point (1289)+point ((1289)+1))/2) ≤ payment (1289)
    have hp : payment 1289 = (1390534839117:ℝ)/1000000000000 := rfl
    have hx : (point 1289+point 1290)/2 = (3877433:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1289
  · change upperValue ((point (1290)+point ((1290)+1))/2) ≤ payment (1290)
    have hp : payment 1290 = (1388408194156:ℝ)/1000000000000 := rfl
    have hx : (point 1290+point 1291)/2 = (3879487:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1290
  · change upperValue ((point (1291)+point ((1291)+1))/2) ≤ payment (1291)
    have hp : payment 1291 = (1386282864552:ℝ)/1000000000000 := rfl
    have hx : (point 1291+point 1292)/2 = (1293847:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1291
  · change upperValue ((point (1292)+point ((1292)+1))/2) ≤ payment (1292)
    have hp : payment 1292 = (1384158847474:ℝ)/1000000000000 := rfl
    have hx : (point 1292+point 1293)/2 = (3883595:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1292
  · change upperValue ((point (1293)+point ((1293)+1))/2) ≤ payment (1293)
    have hp : payment 1293 = (1382036140097:ℝ)/1000000000000 := rfl
    have hx : (point 1293+point 1294)/2 = (3885649:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1293
  · change upperValue ((point (1294)+point ((1294)+1))/2) ≤ payment (1294)
    have hp : payment 1294 = (1379914739601:ℝ)/1000000000000 := rfl
    have hx : (point 1294+point 1295)/2 = (1295901:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1294
  · change upperValue ((point (1295)+point ((1295)+1))/2) ≤ payment (1295)
    have hp : payment 1295 = (1377794643171:ℝ)/1000000000000 := rfl
    have hx : (point 1295+point 1296)/2 = (3889757:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1295
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_080
