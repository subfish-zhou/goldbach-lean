import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints095
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_095 (j : Fin 16) : upperValue ((point (16*95+j.val)+point ((16*95+j.val)+1))/2) ≤ payment (16*95+j.val) := by
  fin_cases j
  · change upperValue ((point (1520)+point ((1520)+1))/2) ≤ payment (1520)
    have hp : payment 1520 = (929019803927:ℝ)/1000000000000 := rfl
    have hx : (point 1520+point 1521)/2 = (4351907:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1520
  · change upperValue ((point (1521)+point ((1521)+1))/2) ≤ payment (1521)
    have hp : payment 1521 = (927130958512:ℝ)/1000000000000 := rfl
    have hx : (point 1521+point 1522)/2 = (4353961:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1521
  · change upperValue ((point (1522)+point ((1522)+1))/2) ≤ payment (1522)
    have hp : payment 1522 = (925242888559:ℝ)/1000000000000 := rfl
    have hx : (point 1522+point 1523)/2 = (1452005:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1522
  · change upperValue ((point (1523)+point ((1523)+1))/2) ≤ payment (1523)
    have hp : payment 1523 = (923355592134:ℝ)/1000000000000 := rfl
    have hx : (point 1523+point 1524)/2 = (4358069:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1523
  · change upperValue ((point (1524)+point ((1524)+1))/2) ≤ payment (1524)
    have hp : payment 1524 = (921469067304:ℝ)/1000000000000 := rfl
    have hx : (point 1524+point 1525)/2 = (4360123:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1524
  · change upperValue ((point (1525)+point ((1525)+1))/2) ≤ payment (1525)
    have hp : payment 1525 = (919583312139:ℝ)/1000000000000 := rfl
    have hx : (point 1525+point 1526)/2 = (1454059:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1525
  · change upperValue ((point (1526)+point ((1526)+1))/2) ≤ payment (1526)
    have hp : payment 1526 = (917698324714:ℝ)/1000000000000 := rfl
    have hx : (point 1526+point 1527)/2 = (4364231:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1526
  · change upperValue ((point (1527)+point ((1527)+1))/2) ≤ payment (1527)
    have hp : payment 1527 = (915814103105:ℝ)/1000000000000 := rfl
    have hx : (point 1527+point 1528)/2 = (4366285:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1527
  · change upperValue ((point (1528)+point ((1528)+1))/2) ≤ payment (1528)
    have hp : payment 1528 = (913930645389:ℝ)/1000000000000 := rfl
    have hx : (point 1528+point 1529)/2 = (1456113:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1528
  · change upperValue ((point (1529)+point ((1529)+1))/2) ≤ payment (1529)
    have hp : payment 1529 = (912047949650:ℝ)/1000000000000 := rfl
    have hx : (point 1529+point 1530)/2 = (4370393:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1529
  · change upperValue ((point (1530)+point ((1530)+1))/2) ≤ payment (1530)
    have hp : payment 1530 = (910166013971:ℝ)/1000000000000 := rfl
    have hx : (point 1530+point 1531)/2 = (4372447:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1530
  · change upperValue ((point (1531)+point ((1531)+1))/2) ≤ payment (1531)
    have hp : payment 1531 = (908284836439:ℝ)/1000000000000 := rfl
    have hx : (point 1531+point 1532)/2 = (1458167:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1531
  · change upperValue ((point (1532)+point ((1532)+1))/2) ≤ payment (1532)
    have hp : payment 1532 = (906404415145:ℝ)/1000000000000 := rfl
    have hx : (point 1532+point 1533)/2 = (4376555:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1532
  · change upperValue ((point (1533)+point ((1533)+1))/2) ≤ payment (1533)
    have hp : payment 1533 = (904524748180:ℝ)/1000000000000 := rfl
    have hx : (point 1533+point 1534)/2 = (4378609:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1533
  · change upperValue ((point (1534)+point ((1534)+1))/2) ≤ payment (1534)
    have hp : payment 1534 = (902645833640:ℝ)/1000000000000 := rfl
    have hx : (point 1534+point 1535)/2 = (1460221:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1534
  · change upperValue ((point (1535)+point ((1535)+1))/2) ≤ payment (1535)
    have hp : payment 1535 = (900767669622:ℝ)/1000000000000 := rfl
    have hx : (point 1535+point 1536)/2 = (4382717:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1535
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_095
