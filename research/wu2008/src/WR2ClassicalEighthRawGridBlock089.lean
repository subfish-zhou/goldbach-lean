import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints089
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_089 (j : Fin 16) : upperValue ((point (16*89+j.val)+point ((16*89+j.val)+1))/2) ≤ payment (16*89+j.val) := by
  fin_cases j
  · change upperValue ((point (1424)+point ((1424)+1))/2) ≤ payment (1424)
    have hp : payment 1424 = (1114264819187:ℝ)/1000000000000 := rfl
    have hx : (point 1424+point 1425)/2 = (4154723:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1424
  · change upperValue ((point (1425)+point ((1425)+1))/2) ≤ payment (1425)
    have hp : payment 1425 = (1112292069442:ℝ)/1000000000000 := rfl
    have hx : (point 1425+point 1426)/2 = (4156777:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1425
  · change upperValue ((point (1426)+point ((1426)+1))/2) ≤ payment (1426)
    have hp : payment 1426 = (1110320295033:ℝ)/1000000000000 := rfl
    have hx : (point 1426+point 1427)/2 = (1386277:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1426
  · change upperValue ((point (1427)+point ((1427)+1))/2) ≤ payment (1427)
    have hp : payment 1427 = (1108349493721:ℝ)/1000000000000 := rfl
    have hx : (point 1427+point 1428)/2 = (4160885:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1427
  · change upperValue ((point (1428)+point ((1428)+1))/2) ≤ payment (1428)
    have hp : payment 1428 = (1106379663270:ℝ)/1000000000000 := rfl
    have hx : (point 1428+point 1429)/2 = (4162939:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1428
  · change upperValue ((point (1429)+point ((1429)+1))/2) ≤ payment (1429)
    have hp : payment 1429 = (1104410801447:ℝ)/1000000000000 := rfl
    have hx : (point 1429+point 1430)/2 = (1388331:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1429
  · change upperValue ((point (1430)+point ((1430)+1))/2) ≤ payment (1430)
    have hp : payment 1430 = (1102442906025:ℝ)/1000000000000 := rfl
    have hx : (point 1430+point 1431)/2 = (4167047:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1430
  · change upperValue ((point (1431)+point ((1431)+1))/2) ≤ payment (1431)
    have hp : payment 1431 = (1100475974777:ℝ)/1000000000000 := rfl
    have hx : (point 1431+point 1432)/2 = (4169101:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1431
  · change upperValue ((point (1432)+point ((1432)+1))/2) ≤ payment (1432)
    have hp : payment 1432 = (1098510005483:ℝ)/1000000000000 := rfl
    have hx : (point 1432+point 1433)/2 = (1390385:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1432
  · change upperValue ((point (1433)+point ((1433)+1))/2) ≤ payment (1433)
    have hp : payment 1433 = (1096544995924:ℝ)/1000000000000 := rfl
    have hx : (point 1433+point 1434)/2 = (4173209:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1433
  · change upperValue ((point (1434)+point ((1434)+1))/2) ≤ payment (1434)
    have hp : payment 1434 = (1094580943887:ℝ)/1000000000000 := rfl
    have hx : (point 1434+point 1435)/2 = (4175263:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1434
  · change upperValue ((point (1435)+point ((1435)+1))/2) ≤ payment (1435)
    have hp : payment 1435 = (1092617847160:ℝ)/1000000000000 := rfl
    have hx : (point 1435+point 1436)/2 = (1392439:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1435
  · change upperValue ((point (1436)+point ((1436)+1))/2) ≤ payment (1436)
    have hp : payment 1436 = (1090655703536:ℝ)/1000000000000 := rfl
    have hx : (point 1436+point 1437)/2 = (4179371:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1436
  · change upperValue ((point (1437)+point ((1437)+1))/2) ≤ payment (1437)
    have hp : payment 1437 = (1088694510811:ℝ)/1000000000000 := rfl
    have hx : (point 1437+point 1438)/2 = (4181425:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1437
  · change upperValue ((point (1438)+point ((1438)+1))/2) ≤ payment (1438)
    have hp : payment 1438 = (1086734266785:ℝ)/1000000000000 := rfl
    have hx : (point 1438+point 1439)/2 = (1394493:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1438
  · change upperValue ((point (1439)+point ((1439)+1))/2) ≤ payment (1439)
    have hp : payment 1439 = (1084774969261:ℝ)/1000000000000 := rfl
    have hx : (point 1439+point 1440)/2 = (4185533:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1439
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_089
