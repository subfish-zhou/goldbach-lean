import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints079
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_079 (j : Fin 16) : upperValue ((point (16*79+j.val)+point ((16*79+j.val)+1))/2) ≤ payment (16*79+j.val) := by
  fin_cases j
  · change upperValue ((point (1264)+point ((1264)+1))/2) ≤ payment (1264)
    have hp : payment 1264 = (1444136842174:ℝ)/1000000000000 := rfl
    have hx : (point 1264+point 1265)/2 = (1275361:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1264
  · change upperValue ((point (1265)+point ((1265)+1))/2) ≤ payment (1265)
    have hp : payment 1265 = (1441976377762:ℝ)/1000000000000 := rfl
    have hx : (point 1265+point 1266)/2 = (3828137:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1265
  · change upperValue ((point (1266)+point ((1266)+1))/2) ≤ payment (1266)
    have hp : payment 1266 = (1439817301215:ℝ)/1000000000000 := rfl
    have hx : (point 1266+point 1267)/2 = (3830191:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1266
  · change upperValue ((point (1267)+point ((1267)+1))/2) ≤ payment (1267)
    have hp : payment 1267 = (1437659609568:ℝ)/1000000000000 := rfl
    have hx : (point 1267+point 1268)/2 = (1277415:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1267
  · change upperValue ((point (1268)+point ((1268)+1))/2) ≤ payment (1268)
    have hp : payment 1268 = (1435503299860:ℝ)/1000000000000 := rfl
    have hx : (point 1268+point 1269)/2 = (3834299:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1268
  · change upperValue ((point (1269)+point ((1269)+1))/2) ≤ payment (1269)
    have hp : payment 1269 = (1433348369135:ℝ)/1000000000000 := rfl
    have hx : (point 1269+point 1270)/2 = (3836353:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1269
  · change upperValue ((point (1270)+point ((1270)+1))/2) ≤ payment (1270)
    have hp : payment 1270 = (1431194814445:ℝ)/1000000000000 := rfl
    have hx : (point 1270+point 1271)/2 = (1279469:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1270
  · change upperValue ((point (1271)+point ((1271)+1))/2) ≤ payment (1271)
    have hp : payment 1271 = (1429042632844:ℝ)/1000000000000 := rfl
    have hx : (point 1271+point 1272)/2 = (3840461:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1271
  · change upperValue ((point (1272)+point ((1272)+1))/2) ≤ payment (1272)
    have hp : payment 1272 = (1426891821394:ℝ)/1000000000000 := rfl
    have hx : (point 1272+point 1273)/2 = (3842515:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1272
  · change upperValue ((point (1273)+point ((1273)+1))/2) ≤ payment (1273)
    have hp : payment 1273 = (1424742377162:ℝ)/1000000000000 := rfl
    have hx : (point 1273+point 1274)/2 = (1281523:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1273
  · change upperValue ((point (1274)+point ((1274)+1))/2) ≤ payment (1274)
    have hp : payment 1274 = (1422594297221:ℝ)/1000000000000 := rfl
    have hx : (point 1274+point 1275)/2 = (3846623:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1274
  · change upperValue ((point (1275)+point ((1275)+1))/2) ≤ payment (1275)
    have hp : payment 1275 = (1420447578650:ℝ)/1000000000000 := rfl
    have hx : (point 1275+point 1276)/2 = (3848677:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1275
  · change upperValue ((point (1276)+point ((1276)+1))/2) ≤ payment (1276)
    have hp : payment 1276 = (1418302218530:ℝ)/1000000000000 := rfl
    have hx : (point 1276+point 1277)/2 = (1283577:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1276
  · change upperValue ((point (1277)+point ((1277)+1))/2) ≤ payment (1277)
    have hp : payment 1277 = (1416158213953:ℝ)/1000000000000 := rfl
    have hx : (point 1277+point 1278)/2 = (3852785:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1277
  · change upperValue ((point (1278)+point ((1278)+1))/2) ≤ payment (1278)
    have hp : payment 1278 = (1414015562011:ℝ)/1000000000000 := rfl
    have hx : (point 1278+point 1279)/2 = (3854839:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1278
  · change upperValue ((point (1279)+point ((1279)+1))/2) ≤ payment (1279)
    have hp : payment 1279 = (1411874259806:ℝ)/1000000000000 := rfl
    have hx : (point 1279+point 1280)/2 = (1285631:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1279
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_079
