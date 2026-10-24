import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints077
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_077 (j : Fin 16) : upperValue ((point (16*77+j.val)+point ((16*77+j.val)+1))/2) ≤ payment (16*77+j.val) := by
  fin_cases j
  · change upperValue ((point (1232)+point ((1232)+1))/2) ≤ payment (1232)
    have hp : payment 1232 = (1514022549306:ℝ)/1000000000000 := rfl
    have hx : (point 1232+point 1233)/2 = (3760355:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1232
  · change upperValue ((point (1233)+point ((1233)+1))/2) ≤ payment (1233)
    have hp : payment 1233 = (1511816072306:ℝ)/1000000000000 := rfl
    have hx : (point 1233+point 1234)/2 = (3762409:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1233
  · change upperValue ((point (1234)+point ((1234)+1))/2) ≤ payment (1234)
    have hp : payment 1234 = (1509611081172:ℝ)/1000000000000 := rfl
    have hx : (point 1234+point 1235)/2 = (1254821:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1234
  · change upperValue ((point (1235)+point ((1235)+1))/2) ≤ payment (1235)
    have hp : payment 1235 = (1507407572749:ℝ)/1000000000000 := rfl
    have hx : (point 1235+point 1236)/2 = (3766517:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1235
  · change upperValue ((point (1236)+point ((1236)+1))/2) ≤ payment (1236)
    have hp : payment 1236 = (1505205543887:ℝ)/1000000000000 := rfl
    have hx : (point 1236+point 1237)/2 = (3768571:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1236
  · change upperValue ((point (1237)+point ((1237)+1))/2) ≤ payment (1237)
    have hp : payment 1237 = (1503004991443:ℝ)/1000000000000 := rfl
    have hx : (point 1237+point 1238)/2 = (1256875:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1237
  · change upperValue ((point (1238)+point ((1238)+1))/2) ≤ payment (1238)
    have hp : payment 1238 = (1500805912280:ℝ)/1000000000000 := rfl
    have hx : (point 1238+point 1239)/2 = (3772679:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1238
  · change upperValue ((point (1239)+point ((1239)+1))/2) ≤ payment (1239)
    have hp : payment 1239 = (1498608303267:ℝ)/1000000000000 := rfl
    have hx : (point 1239+point 1240)/2 = (3774733:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1239
  · change upperValue ((point (1240)+point ((1240)+1))/2) ≤ payment (1240)
    have hp : payment 1240 = (1496412161280:ℝ)/1000000000000 := rfl
    have hx : (point 1240+point 1241)/2 = (1258929:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1240
  · change upperValue ((point (1241)+point ((1241)+1))/2) ≤ payment (1241)
    have hp : payment 1241 = (1494217483199:ℝ)/1000000000000 := rfl
    have hx : (point 1241+point 1242)/2 = (3778841:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1241
  · change upperValue ((point (1242)+point ((1242)+1))/2) ≤ payment (1242)
    have hp : payment 1242 = (1492024265913:ℝ)/1000000000000 := rfl
    have hx : (point 1242+point 1243)/2 = (3780895:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1242
  · change upperValue ((point (1243)+point ((1243)+1))/2) ≤ payment (1243)
    have hp : payment 1243 = (1489832506315:ℝ)/1000000000000 := rfl
    have hx : (point 1243+point 1244)/2 = (1260983:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1243
  · change upperValue ((point (1244)+point ((1244)+1))/2) ≤ payment (1244)
    have hp : payment 1244 = (1487642201303:ℝ)/1000000000000 := rfl
    have hx : (point 1244+point 1245)/2 = (3785003:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1244
  · change upperValue ((point (1245)+point ((1245)+1))/2) ≤ payment (1245)
    have hp : payment 1245 = (1485453347784:ℝ)/1000000000000 := rfl
    have hx : (point 1245+point 1246)/2 = (3787057:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1245
  · change upperValue ((point (1246)+point ((1246)+1))/2) ≤ payment (1246)
    have hp : payment 1246 = (1483265942669:ℝ)/1000000000000 := rfl
    have hx : (point 1246+point 1247)/2 = (1263037:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1246
  · change upperValue ((point (1247)+point ((1247)+1))/2) ≤ payment (1247)
    have hp : payment 1247 = (1481079982875:ℝ)/1000000000000 := rfl
    have hx : (point 1247+point 1248)/2 = (3791165:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1247
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_077
