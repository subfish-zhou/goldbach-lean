import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints087
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_087 (j : Fin 16) : upperValue ((point (16*87+j.val)+point ((16*87+j.val)+1))/2) ≤ payment (16*87+j.val) := by
  fin_cases j
  · change upperValue ((point (1392)+point ((1392)+1))/2) ≤ payment (1392)
    have hp : payment 1392 = (1177921381705:ℝ)/1000000000000 := rfl
    have hx : (point 1392+point 1393)/2 = (4088995:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1392
  · change upperValue ((point (1393)+point ((1393)+1))/2) ≤ payment (1393)
    have hp : payment 1393 = (1175916216691:ℝ)/1000000000000 := rfl
    have hx : (point 1393+point 1394)/2 = (1363683:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1393
  · change upperValue ((point (1394)+point ((1394)+1))/2) ≤ payment (1394)
    have hp : payment 1394 = (1173912100639:ℝ)/1000000000000 := rfl
    have hx : (point 1394+point 1395)/2 = (4093103:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1394
  · change upperValue ((point (1395)+point ((1395)+1))/2) ≤ payment (1395)
    have hp : payment 1395 = (1171909031188:ℝ)/1000000000000 := rfl
    have hx : (point 1395+point 1396)/2 = (4095157:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1395
  · change upperValue ((point (1396)+point ((1396)+1))/2) ≤ payment (1396)
    have hp : payment 1396 = (1169907005982:ℝ)/1000000000000 := rfl
    have hx : (point 1396+point 1397)/2 = (1365737:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1396
  · change upperValue ((point (1397)+point ((1397)+1))/2) ≤ payment (1397)
    have hp : payment 1397 = (1167906022670:ℝ)/1000000000000 := rfl
    have hx : (point 1397+point 1398)/2 = (4099265:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1397
  · change upperValue ((point (1398)+point ((1398)+1))/2) ≤ payment (1398)
    have hp : payment 1398 = (1165906078902:ℝ)/1000000000000 := rfl
    have hx : (point 1398+point 1399)/2 = (4101319:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1398
  · change upperValue ((point (1399)+point ((1399)+1))/2) ≤ payment (1399)
    have hp : payment 1399 = (1163907172334:ℝ)/1000000000000 := rfl
    have hx : (point 1399+point 1400)/2 = (1367791:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1399
  · change upperValue ((point (1400)+point ((1400)+1))/2) ≤ payment (1400)
    have hp : payment 1400 = (1161909300626:ℝ)/1000000000000 := rfl
    have hx : (point 1400+point 1401)/2 = (4105427:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1400
  · change upperValue ((point (1401)+point ((1401)+1))/2) ≤ payment (1401)
    have hp : payment 1401 = (1159912461440:ℝ)/1000000000000 := rfl
    have hx : (point 1401+point 1402)/2 = (4107481:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1401
  · change upperValue ((point (1402)+point ((1402)+1))/2) ≤ payment (1402)
    have hp : payment 1402 = (1157916652444:ℝ)/1000000000000 := rfl
    have hx : (point 1402+point 1403)/2 = (1369845:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1402
  · change upperValue ((point (1403)+point ((1403)+1))/2) ≤ payment (1403)
    have hp : payment 1403 = (1155921871309:ℝ)/1000000000000 := rfl
    have hx : (point 1403+point 1404)/2 = (4111589:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1403
  · change upperValue ((point (1404)+point ((1404)+1))/2) ≤ payment (1404)
    have hp : payment 1404 = (1153928115710:ℝ)/1000000000000 := rfl
    have hx : (point 1404+point 1405)/2 = (4113643:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1404
  · change upperValue ((point (1405)+point ((1405)+1))/2) ≤ payment (1405)
    have hp : payment 1405 = (1151935383326:ℝ)/1000000000000 := rfl
    have hx : (point 1405+point 1406)/2 = (1371899:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1405
  · change upperValue ((point (1406)+point ((1406)+1))/2) ≤ payment (1406)
    have hp : payment 1406 = (1149943671838:ℝ)/1000000000000 := rfl
    have hx : (point 1406+point 1407)/2 = (4117751:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1406
  · change upperValue ((point (1407)+point ((1407)+1))/2) ≤ payment (1407)
    have hp : payment 1407 = (1147952978934:ℝ)/1000000000000 := rfl
    have hx : (point 1407+point 1408)/2 = (4119805:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1407
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_087
