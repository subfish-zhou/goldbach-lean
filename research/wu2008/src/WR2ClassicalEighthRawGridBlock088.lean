import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints088
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_088 (j : Fin 16) : upperValue ((point (16*88+j.val)+point ((16*88+j.val)+1))/2) ≤ payment (16*88+j.val) := by
  fin_cases j
  · change upperValue ((point (1408)+point ((1408)+1))/2) ≤ payment (1408)
    have hp : payment 1408 = (1145963302303:ℝ)/1000000000000 := rfl
    have hx : (point 1408+point 1409)/2 = (1373953:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1408
  · change upperValue ((point (1409)+point ((1409)+1))/2) ≤ payment (1409)
    have hp : payment 1409 = (1143974639640:ℝ)/1000000000000 := rfl
    have hx : (point 1409+point 1410)/2 = (4123913:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1409
  · change upperValue ((point (1410)+point ((1410)+1))/2) ≤ payment (1410)
    have hp : payment 1410 = (1141986988642:ℝ)/1000000000000 := rfl
    have hx : (point 1410+point 1411)/2 = (4125967:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1410
  · change upperValue ((point (1411)+point ((1411)+1))/2) ≤ payment (1411)
    have hp : payment 1411 = (1140000347010:ℝ)/1000000000000 := rfl
    have hx : (point 1411+point 1412)/2 = (1376007:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1411
  · change upperValue ((point (1412)+point ((1412)+1))/2) ≤ payment (1412)
    have hp : payment 1412 = (1138014712451:ℝ)/1000000000000 := rfl
    have hx : (point 1412+point 1413)/2 = (4130075:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1412
  · change upperValue ((point (1413)+point ((1413)+1))/2) ≤ payment (1413)
    have hp : payment 1413 = (1136030082673:ℝ)/1000000000000 := rfl
    have hx : (point 1413+point 1414)/2 = (4132129:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1413
  · change upperValue ((point (1414)+point ((1414)+1))/2) ≤ payment (1414)
    have hp : payment 1414 = (1134046455389:ℝ)/1000000000000 := rfl
    have hx : (point 1414+point 1415)/2 = (1378061:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1414
  · change upperValue ((point (1415)+point ((1415)+1))/2) ≤ payment (1415)
    have hp : payment 1415 = (1132063828315:ℝ)/1000000000000 := rfl
    have hx : (point 1415+point 1416)/2 = (4136237:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1415
  · change upperValue ((point (1416)+point ((1416)+1))/2) ≤ payment (1416)
    have hp : payment 1416 = (1130082199172:ℝ)/1000000000000 := rfl
    have hx : (point 1416+point 1417)/2 = (4138291:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1416
  · change upperValue ((point (1417)+point ((1417)+1))/2) ≤ payment (1417)
    have hp : payment 1417 = (1128101565684:ℝ)/1000000000000 := rfl
    have hx : (point 1417+point 1418)/2 = (1380115:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1417
  · change upperValue ((point (1418)+point ((1418)+1))/2) ≤ payment (1418)
    have hp : payment 1418 = (1126121925578:ℝ)/1000000000000 := rfl
    have hx : (point 1418+point 1419)/2 = (4142399:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1418
  · change upperValue ((point (1419)+point ((1419)+1))/2) ≤ payment (1419)
    have hp : payment 1419 = (1124143276585:ℝ)/1000000000000 := rfl
    have hx : (point 1419+point 1420)/2 = (4144453:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1419
  · change upperValue ((point (1420)+point ((1420)+1))/2) ≤ payment (1420)
    have hp : payment 1420 = (1122165616442:ℝ)/1000000000000 := rfl
    have hx : (point 1420+point 1421)/2 = (1382169:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1420
  · change upperValue ((point (1421)+point ((1421)+1))/2) ≤ payment (1421)
    have hp : payment 1421 = (1120188942886:ℝ)/1000000000000 := rfl
    have hx : (point 1421+point 1422)/2 = (4148561:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1421
  · change upperValue ((point (1422)+point ((1422)+1))/2) ≤ payment (1422)
    have hp : payment 1422 = (1118213253660:ℝ)/1000000000000 := rfl
    have hx : (point 1422+point 1423)/2 = (4150615:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1422
  · change upperValue ((point (1423)+point ((1423)+1))/2) ≤ payment (1423)
    have hp : payment 1423 = (1116238546511:ℝ)/1000000000000 := rfl
    have hx : (point 1423+point 1424)/2 = (1384223:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1423
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_088
