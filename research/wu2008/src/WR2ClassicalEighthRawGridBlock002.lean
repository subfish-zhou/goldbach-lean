import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints002
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_002 (j : Fin 16) : upperValue ((point (16*2+j.val)+point ((16*2+j.val)+1))/2) ≤ payment (16*2+j.val) := by
  fin_cases j
  · change upperValue ((point (32)+point ((32)+1))/2) ≤ payment (32)
    have hp : payment 32 = (7742055327282:ℝ)/1000000000000 := rfl
    have hx : (point 32+point 33)/2 = (1295555:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_32
  · change upperValue ((point (33)+point ((33)+1))/2) ≤ payment (33)
    have hp : payment 33 = (7727929205576:ℝ)/1000000000000 := rfl
    have hx : (point 33+point 34)/2 = (1297609:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_33
  · change upperValue ((point (34)+point ((34)+1))/2) ≤ payment (34)
    have hp : payment 34 = (7713846594980:ℝ)/1000000000000 := rfl
    have hx : (point 34+point 35)/2 = (433221:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_34
  · change upperValue ((point (35)+point ((35)+1))/2) ≤ payment (35)
    have hp : payment 35 = (7699807288787:ℝ)/1000000000000 := rfl
    have hx : (point 35+point 36)/2 = (1301717:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_35
  · change upperValue ((point (36)+point ((36)+1))/2) ≤ payment (36)
    have hp : payment 36 = (7685811081594:ℝ)/1000000000000 := rfl
    have hx : (point 36+point 37)/2 = (1303771:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_36
  · change upperValue ((point (37)+point ((37)+1))/2) ≤ payment (37)
    have hp : payment 37 = (7671857769286:ℝ)/1000000000000 := rfl
    have hx : (point 37+point 38)/2 = (435275:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_37
  · change upperValue ((point (38)+point ((38)+1))/2) ≤ payment (38)
    have hp : payment 38 = (7657947149034:ℝ)/1000000000000 := rfl
    have hx : (point 38+point 39)/2 = (1307879:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_38
  · change upperValue ((point (39)+point ((39)+1))/2) ≤ payment (39)
    have hp : payment 39 = (7644079019277:ℝ)/1000000000000 := rfl
    have hx : (point 39+point 40)/2 = (1309933:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_39
  · change upperValue ((point (40)+point ((40)+1))/2) ≤ payment (40)
    have hp : payment 40 = (7630253179718:ℝ)/1000000000000 := rfl
    have hx : (point 40+point 41)/2 = (437329:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_40
  · change upperValue ((point (41)+point ((41)+1))/2) ≤ payment (41)
    have hp : payment 41 = (7616469431309:ℝ)/1000000000000 := rfl
    have hx : (point 41+point 42)/2 = (1314041:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_41
  · change upperValue ((point (42)+point ((42)+1))/2) ≤ payment (42)
    have hp : payment 42 = (7602727576248:ℝ)/1000000000000 := rfl
    have hx : (point 42+point 43)/2 = (1316095:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_42
  · change upperValue ((point (43)+point ((43)+1))/2) ≤ payment (43)
    have hp : payment 43 = (7589027417962:ℝ)/1000000000000 := rfl
    have hx : (point 43+point 44)/2 = (439383:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_43
  · change upperValue ((point (44)+point ((44)+1))/2) ≤ payment (44)
    have hp : payment 44 = (7575368761103:ℝ)/1000000000000 := rfl
    have hx : (point 44+point 45)/2 = (1320203:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_44
  · change upperValue ((point (45)+point ((45)+1))/2) ≤ payment (45)
    have hp : payment 45 = (7561751411534:ℝ)/1000000000000 := rfl
    have hx : (point 45+point 46)/2 = (1322257:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_45
  · change upperValue ((point (46)+point ((46)+1))/2) ≤ payment (46)
    have hp : payment 46 = (7548175176323:ℝ)/1000000000000 := rfl
    have hx : (point 46+point 47)/2 = (441437:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_46
  · change upperValue ((point (47)+point ((47)+1))/2) ≤ payment (47)
    have hp : payment 47 = (7534639863733:ℝ)/1000000000000 := rfl
    have hx : (point 47+point 48)/2 = (1326365:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_47
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_002
