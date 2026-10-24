import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints090
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_090 (j : Fin 16) : upperValue ((point (16*90+j.val)+point ((16*90+j.val)+1))/2) ≤ payment (16*90+j.val) := by
  fin_cases j
  · change upperValue ((point (1440)+point ((1440)+1))/2) ≤ payment (1440)
    have hp : payment 1440 = (1082816616046:ℝ)/1000000000000 := rfl
    have hx : (point 1440+point 1441)/2 = (4187587:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1440
  · change upperValue ((point (1441)+point ((1441)+1))/2) ≤ payment (1441)
    have hp : payment 1441 = (1080859204950:ℝ)/1000000000000 := rfl
    have hx : (point 1441+point 1442)/2 = (1396547:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1441
  · change upperValue ((point (1442)+point ((1442)+1))/2) ≤ payment (1442)
    have hp : payment 1442 = (1078902733786:ℝ)/1000000000000 := rfl
    have hx : (point 1442+point 1443)/2 = (4191695:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1442
  · change upperValue ((point (1443)+point ((1443)+1))/2) ≤ payment (1443)
    have hp : payment 1443 = (1076947200372:ℝ)/1000000000000 := rfl
    have hx : (point 1443+point 1444)/2 = (4193749:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1443
  · change upperValue ((point (1444)+point ((1444)+1))/2) ≤ payment (1444)
    have hp : payment 1444 = (1074992602529:ℝ)/1000000000000 := rfl
    have hx : (point 1444+point 1445)/2 = (1398601:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1444
  · change upperValue ((point (1445)+point ((1445)+1))/2) ≤ payment (1445)
    have hp : payment 1445 = (1073038938079:ℝ)/1000000000000 := rfl
    have hx : (point 1445+point 1446)/2 = (4197857:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1445
  · change upperValue ((point (1446)+point ((1446)+1))/2) ≤ payment (1446)
    have hp : payment 1446 = (1071086204852:ℝ)/1000000000000 := rfl
    have hx : (point 1446+point 1447)/2 = (4199911:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1446
  · change upperValue ((point (1447)+point ((1447)+1))/2) ≤ payment (1447)
    have hp : payment 1447 = (1069134400676:ℝ)/1000000000000 := rfl
    have hx : (point 1447+point 1448)/2 = (1400655:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1447
  · change upperValue ((point (1448)+point ((1448)+1))/2) ≤ payment (1448)
    have hp : payment 1448 = (1067183523388:ℝ)/1000000000000 := rfl
    have hx : (point 1448+point 1449)/2 = (4204019:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1448
  · change upperValue ((point (1449)+point ((1449)+1))/2) ≤ payment (1449)
    have hp : payment 1449 = (1065233570824:ℝ)/1000000000000 := rfl
    have hx : (point 1449+point 1450)/2 = (4206073:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1449
  · change upperValue ((point (1450)+point ((1450)+1))/2) ≤ payment (1450)
    have hp : payment 1450 = (1063284540825:ℝ)/1000000000000 := rfl
    have hx : (point 1450+point 1451)/2 = (1402709:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1450
  · change upperValue ((point (1451)+point ((1451)+1))/2) ≤ payment (1451)
    have hp : payment 1451 = (1061336431236:ℝ)/1000000000000 := rfl
    have hx : (point 1451+point 1452)/2 = (4210181:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1451
  · change upperValue ((point (1452)+point ((1452)+1))/2) ≤ payment (1452)
    have hp : payment 1452 = (1059389239905:ℝ)/1000000000000 := rfl
    have hx : (point 1452+point 1453)/2 = (4212235:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1452
  · change upperValue ((point (1453)+point ((1453)+1))/2) ≤ payment (1453)
    have hp : payment 1453 = (1057442964683:ℝ)/1000000000000 := rfl
    have hx : (point 1453+point 1454)/2 = (1404763:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1453
  · change upperValue ((point (1454)+point ((1454)+1))/2) ≤ payment (1454)
    have hp : payment 1454 = (1055497603424:ℝ)/1000000000000 := rfl
    have hx : (point 1454+point 1455)/2 = (4216343:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1454
  · change upperValue ((point (1455)+point ((1455)+1))/2) ≤ payment (1455)
    have hp : payment 1455 = (1053553153986:ℝ)/1000000000000 := rfl
    have hx : (point 1455+point 1456)/2 = (4218397:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1455
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_090
