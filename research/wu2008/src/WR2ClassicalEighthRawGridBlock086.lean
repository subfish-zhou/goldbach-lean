import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints086
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_086 (j : Fin 16) : upperValue ((point (16*86+j.val)+point ((16*86+j.val)+1))/2) ≤ payment (16*86+j.val) := by
  fin_cases j
  · change upperValue ((point (1376)+point ((1376)+1))/2) ≤ payment (1376)
    have hp : payment 1376 = (1210148622082:ℝ)/1000000000000 := rfl
    have hx : (point 1376+point 1377)/2 = (4056131:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1376
  · change upperValue ((point (1377)+point ((1377)+1))/2) ≤ payment (1377)
    have hp : payment 1377 = (1208126349438:ℝ)/1000000000000 := rfl
    have hx : (point 1377+point 1378)/2 = (4058185:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1377
  · change upperValue ((point (1378)+point ((1378)+1))/2) ≤ payment (1378)
    have hp : payment 1378 = (1206105164063:ℝ)/1000000000000 := rfl
    have hx : (point 1378+point 1379)/2 = (1353413:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1378
  · change upperValue ((point (1379)+point ((1379)+1))/2) ≤ payment (1379)
    have hp : payment 1379 = (1204085063532:ℝ)/1000000000000 := rfl
    have hx : (point 1379+point 1380)/2 = (4062293:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1379
  · change upperValue ((point (1380)+point ((1380)+1))/2) ≤ payment (1380)
    have hp : payment 1380 = (1202066045426:ℝ)/1000000000000 := rfl
    have hx : (point 1380+point 1381)/2 = (4064347:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1380
  · change upperValue ((point (1381)+point ((1381)+1))/2) ≤ payment (1381)
    have hp : payment 1381 = (1200048107327:ℝ)/1000000000000 := rfl
    have hx : (point 1381+point 1382)/2 = (1355467:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1381
  · change upperValue ((point (1382)+point ((1382)+1))/2) ≤ payment (1382)
    have hp : payment 1382 = (1198031246824:ℝ)/1000000000000 := rfl
    have hx : (point 1382+point 1383)/2 = (4068455:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1382
  · change upperValue ((point (1383)+point ((1383)+1))/2) ≤ payment (1383)
    have hp : payment 1383 = (1196015461507:ℝ)/1000000000000 := rfl
    have hx : (point 1383+point 1384)/2 = (4070509:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1383
  · change upperValue ((point (1384)+point ((1384)+1))/2) ≤ payment (1384)
    have hp : payment 1384 = (1194000748973:ℝ)/1000000000000 := rfl
    have hx : (point 1384+point 1385)/2 = (1023:ℝ)/4096 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1384
  · change upperValue ((point (1385)+point ((1385)+1))/2) ≤ payment (1385)
    have hp : payment 1385 = (1191987106822:ℝ)/1000000000000 := rfl
    have hx : (point 1385+point 1386)/2 = (4074617:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1385
  · change upperValue ((point (1386)+point ((1386)+1))/2) ≤ payment (1386)
    have hp : payment 1386 = (1189974532657:ℝ)/1000000000000 := rfl
    have hx : (point 1386+point 1387)/2 = (4076671:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1386
  · change upperValue ((point (1387)+point ((1387)+1))/2) ≤ payment (1387)
    have hp : payment 1387 = (1187963024086:ℝ)/1000000000000 := rfl
    have hx : (point 1387+point 1388)/2 = (1359575:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1387
  · change upperValue ((point (1388)+point ((1388)+1))/2) ≤ payment (1388)
    have hp : payment 1388 = (1185952578722:ℝ)/1000000000000 := rfl
    have hx : (point 1388+point 1389)/2 = (4080779:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1388
  · change upperValue ((point (1389)+point ((1389)+1))/2) ≤ payment (1389)
    have hp : payment 1389 = (1183943194179:ℝ)/1000000000000 := rfl
    have hx : (point 1389+point 1390)/2 = (4082833:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1389
  · change upperValue ((point (1390)+point ((1390)+1))/2) ≤ payment (1390)
    have hp : payment 1390 = (1181934868079:ℝ)/1000000000000 := rfl
    have hx : (point 1390+point 1391)/2 = (1361629:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1390
  · change upperValue ((point (1391)+point ((1391)+1))/2) ≤ payment (1391)
    have hp : payment 1391 = (1179927598045:ℝ)/1000000000000 := rfl
    have hx : (point 1391+point 1392)/2 = (4086941:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1391
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_086
