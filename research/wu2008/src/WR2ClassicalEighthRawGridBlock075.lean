import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints075
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_075 (j : Fin 16) : upperValue ((point (16*75+j.val)+point ((16*75+j.val)+1))/2) ≤ payment (16*75+j.val) := by
  fin_cases j
  · change upperValue ((point (1200)+point ((1200)+1))/2) ≤ payment (1200)
    have hp : payment 1200 = (1585433562459:ℝ)/1000000000000 := rfl
    have hx : (point 1200+point 1201)/2 = (3694627:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1200
  · change upperValue ((point (1201)+point ((1201)+1))/2) ≤ payment (1201)
    have hp : payment 1201 = (1583177833816:ℝ)/1000000000000 := rfl
    have hx : (point 1201+point 1202)/2 = (1232227:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1201
  · change upperValue ((point (1202)+point ((1202)+1))/2) ≤ payment (1202)
    have hp : payment 1202 = (1580923695379:ℝ)/1000000000000 := rfl
    have hx : (point 1202+point 1203)/2 = (3698735:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1202
  · change upperValue ((point (1203)+point ((1203)+1))/2) ≤ payment (1203)
    have hp : payment 1203 = (1578671143785:ℝ)/1000000000000 := rfl
    have hx : (point 1203+point 1204)/2 = (3700789:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1203
  · change upperValue ((point (1204)+point ((1204)+1))/2) ≤ payment (1204)
    have hp : payment 1204 = (1576420175679:ℝ)/1000000000000 := rfl
    have hx : (point 1204+point 1205)/2 = (1234281:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1204
  · change upperValue ((point (1205)+point ((1205)+1))/2) ≤ payment (1205)
    have hp : payment 1205 = (1574170787711:ℝ)/1000000000000 := rfl
    have hx : (point 1205+point 1206)/2 = (3704897:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1205
  · change upperValue ((point (1206)+point ((1206)+1))/2) ≤ payment (1206)
    have hp : payment 1206 = (1571922976540:ℝ)/1000000000000 := rfl
    have hx : (point 1206+point 1207)/2 = (3706951:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1206
  · change upperValue ((point (1207)+point ((1207)+1))/2) ≤ payment (1207)
    have hp : payment 1207 = (1569676738829:ℝ)/1000000000000 := rfl
    have hx : (point 1207+point 1208)/2 = (1236335:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1207
  · change upperValue ((point (1208)+point ((1208)+1))/2) ≤ payment (1208)
    have hp : payment 1208 = (1567432071251:ℝ)/1000000000000 := rfl
    have hx : (point 1208+point 1209)/2 = (3711059:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1208
  · change upperValue ((point (1209)+point ((1209)+1))/2) ≤ payment (1209)
    have hp : payment 1209 = (1565188970482:ℝ)/1000000000000 := rfl
    have hx : (point 1209+point 1210)/2 = (3713113:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1209
  · change upperValue ((point (1210)+point ((1210)+1))/2) ≤ payment (1210)
    have hp : payment 1210 = (1562947433207:ℝ)/1000000000000 := rfl
    have hx : (point 1210+point 1211)/2 = (1238389:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1210
  · change upperValue ((point (1211)+point ((1211)+1))/2) ≤ payment (1211)
    have hp : payment 1211 = (1560707456117:ℝ)/1000000000000 := rfl
    have hx : (point 1211+point 1212)/2 = (3717221:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1211
  · change upperValue ((point (1212)+point ((1212)+1))/2) ≤ payment (1212)
    have hp : payment 1212 = (1558469035910:ℝ)/1000000000000 := rfl
    have hx : (point 1212+point 1213)/2 = (3719275:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1212
  · change upperValue ((point (1213)+point ((1213)+1))/2) ≤ payment (1213)
    have hp : payment 1213 = (1556232169291:ℝ)/1000000000000 := rfl
    have hx : (point 1213+point 1214)/2 = (1240443:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1213
  · change upperValue ((point (1214)+point ((1214)+1))/2) ≤ payment (1214)
    have hp : payment 1214 = (1553996852969:ℝ)/1000000000000 := rfl
    have hx : (point 1214+point 1215)/2 = (3723383:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1214
  · change upperValue ((point (1215)+point ((1215)+1))/2) ≤ payment (1215)
    have hp : payment 1215 = (1551763083662:ℝ)/1000000000000 := rfl
    have hx : (point 1215+point 1216)/2 = (3725437:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1215
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_075
