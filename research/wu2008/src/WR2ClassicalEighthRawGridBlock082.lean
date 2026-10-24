import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints082
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_082 (j : Fin 16) : upperValue ((point (16*82+j.val)+point ((16*82+j.val)+1))/2) ≤ payment (16*82+j.val) := by
  fin_cases j
  · change upperValue ((point (1312)+point ((1312)+1))/2) ≤ payment (1312)
    have hp : payment 1312 = (1341949823534:ℝ)/1000000000000 := rfl
    have hx : (point 1312+point 1313)/2 = (1308225:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1312
  · change upperValue ((point (1313)+point ((1313)+1))/2) ≤ payment (1313)
    have hp : payment 1313 = (1339852724842:ℝ)/1000000000000 := rfl
    have hx : (point 1313+point 1314)/2 = (3926729:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1313
  · change upperValue ((point (1314)+point ((1314)+1))/2) ≤ payment (1314)
    have hp : payment 1314 = (1337756877709:ℝ)/1000000000000 := rfl
    have hx : (point 1314+point 1315)/2 = (3928783:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1314
  · change upperValue ((point (1315)+point ((1315)+1))/2) ≤ payment (1315)
    have hp : payment 1315 = (1335662279421:ℝ)/1000000000000 := rfl
    have hx : (point 1315+point 1316)/2 = (1310279:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1315
  · change upperValue ((point (1316)+point ((1316)+1))/2) ≤ payment (1316)
    have hp : payment 1316 = (1333568927271:ℝ)/1000000000000 := rfl
    have hx : (point 1316+point 1317)/2 = (3932891:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1316
  · change upperValue ((point (1317)+point ((1317)+1))/2) ≤ payment (1317)
    have hp : payment 1317 = (1331476818553:ℝ)/1000000000000 := rfl
    have hx : (point 1317+point 1318)/2 = (3934945:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1317
  · change upperValue ((point (1318)+point ((1318)+1))/2) ≤ payment (1318)
    have hp : payment 1318 = (1329385950570:ℝ)/1000000000000 := rfl
    have hx : (point 1318+point 1319)/2 = (1312333:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1318
  · change upperValue ((point (1319)+point ((1319)+1))/2) ≤ payment (1319)
    have hp : payment 1319 = (1327296320628:ℝ)/1000000000000 := rfl
    have hx : (point 1319+point 1320)/2 = (3939053:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1319
  · change upperValue ((point (1320)+point ((1320)+1))/2) ≤ payment (1320)
    have hp : payment 1320 = (1325207926038:ℝ)/1000000000000 := rfl
    have hx : (point 1320+point 1321)/2 = (3941107:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1320
  · change upperValue ((point (1321)+point ((1321)+1))/2) ≤ payment (1321)
    have hp : payment 1321 = (1323120764116:ℝ)/1000000000000 := rfl
    have hx : (point 1321+point 1322)/2 = (1314387:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1321
  · change upperValue ((point (1322)+point ((1322)+1))/2) ≤ payment (1322)
    have hp : payment 1322 = (1321034832182:ℝ)/1000000000000 := rfl
    have hx : (point 1322+point 1323)/2 = (3945215:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1322
  · change upperValue ((point (1323)+point ((1323)+1))/2) ≤ payment (1323)
    have hp : payment 1323 = (1318950127562:ℝ)/1000000000000 := rfl
    have hx : (point 1323+point 1324)/2 = (3947269:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1323
  · change upperValue ((point (1324)+point ((1324)+1))/2) ≤ payment (1324)
    have hp : payment 1324 = (1316866647587:ℝ)/1000000000000 := rfl
    have hx : (point 1324+point 1325)/2 = (1316441:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1324
  · change upperValue ((point (1325)+point ((1325)+1))/2) ≤ payment (1325)
    have hp : payment 1325 = (1314784389592:ℝ)/1000000000000 := rfl
    have hx : (point 1325+point 1326)/2 = (3951377:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1325
  · change upperValue ((point (1326)+point ((1326)+1))/2) ≤ payment (1326)
    have hp : payment 1326 = (1312703350916:ℝ)/1000000000000 := rfl
    have hx : (point 1326+point 1327)/2 = (3953431:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1326
  · change upperValue ((point (1327)+point ((1327)+1))/2) ≤ payment (1327)
    have hp : payment 1327 = (1310623528904:ℝ)/1000000000000 := rfl
    have hx : (point 1327+point 1328)/2 = (1318495:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1327
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_082
