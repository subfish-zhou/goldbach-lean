import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints078
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_078 (j : Fin 16) : upperValue ((point (16*78+j.val)+point ((16*78+j.val)+1))/2) ≤ payment (16*78+j.val) := by
  fin_cases j
  · change upperValue ((point (1248)+point ((1248)+1))/2) ≤ payment (1248)
    have hp : payment 1248 = (1478895465327:ℝ)/1000000000000 := rfl
    have hx : (point 1248+point 1249)/2 = (3793219:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1248
  · change upperValue ((point (1249)+point ((1249)+1))/2) ≤ payment (1249)
    have hp : payment 1249 = (1476712386952:ℝ)/1000000000000 := rfl
    have hx : (point 1249+point 1250)/2 = (1265091:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1249
  · change upperValue ((point (1250)+point ((1250)+1))/2) ≤ payment (1250)
    have hp : payment 1250 = (1474530744687:ℝ)/1000000000000 := rfl
    have hx : (point 1250+point 1251)/2 = (3797327:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1250
  · change upperValue ((point (1251)+point ((1251)+1))/2) ≤ payment (1251)
    have hp : payment 1251 = (1472350535472:ℝ)/1000000000000 := rfl
    have hx : (point 1251+point 1252)/2 = (3799381:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1251
  · change upperValue ((point (1252)+point ((1252)+1))/2) ≤ payment (1252)
    have hp : payment 1252 = (1470171756255:ℝ)/1000000000000 := rfl
    have hx : (point 1252+point 1253)/2 = (1267145:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1252
  · change upperValue ((point (1253)+point ((1253)+1))/2) ≤ payment (1253)
    have hp : payment 1253 = (1467994403988:ℝ)/1000000000000 := rfl
    have hx : (point 1253+point 1254)/2 = (3803489:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1253
  · change upperValue ((point (1254)+point ((1254)+1))/2) ≤ payment (1254)
    have hp : payment 1254 = (1465818475632:ℝ)/1000000000000 := rfl
    have hx : (point 1254+point 1255)/2 = (3805543:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1254
  · change upperValue ((point (1255)+point ((1255)+1))/2) ≤ payment (1255)
    have hp : payment 1255 = (1463643968149:ℝ)/1000000000000 := rfl
    have hx : (point 1255+point 1256)/2 = (1269199:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1255
  · change upperValue ((point (1256)+point ((1256)+1))/2) ≤ payment (1256)
    have hp : payment 1256 = (1461470878510:ℝ)/1000000000000 := rfl
    have hx : (point 1256+point 1257)/2 = (3809651:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1256
  · change upperValue ((point (1257)+point ((1257)+1))/2) ≤ payment (1257)
    have hp : payment 1257 = (1459299203693:ℝ)/1000000000000 := rfl
    have hx : (point 1257+point 1258)/2 = (3811705:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1257
  · change upperValue ((point (1258)+point ((1258)+1))/2) ≤ payment (1258)
    have hp : payment 1258 = (1457128940678:ℝ)/1000000000000 := rfl
    have hx : (point 1258+point 1259)/2 = (1271253:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1258
  · change upperValue ((point (1259)+point ((1259)+1))/2) ≤ payment (1259)
    have hp : payment 1259 = (1454960086454:ℝ)/1000000000000 := rfl
    have hx : (point 1259+point 1260)/2 = (3815813:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1259
  · change upperValue ((point (1260)+point ((1260)+1))/2) ≤ payment (1260)
    have hp : payment 1260 = (1452792638015:ℝ)/1000000000000 := rfl
    have hx : (point 1260+point 1261)/2 = (3817867:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1260
  · change upperValue ((point (1261)+point ((1261)+1))/2) ≤ payment (1261)
    have hp : payment 1261 = (1450626592359:ℝ)/1000000000000 := rfl
    have hx : (point 1261+point 1262)/2 = (1273307:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1261
  · change upperValue ((point (1262)+point ((1262)+1))/2) ≤ payment (1262)
    have hp : payment 1262 = (1448461946492:ℝ)/1000000000000 := rfl
    have hx : (point 1262+point 1263)/2 = (3821975:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1262
  · change upperValue ((point (1263)+point ((1263)+1))/2) ≤ payment (1263)
    have hp : payment 1263 = (1446298697425:ℝ)/1000000000000 := rfl
    have hx : (point 1263+point 1264)/2 = (3824029:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1263
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_078
