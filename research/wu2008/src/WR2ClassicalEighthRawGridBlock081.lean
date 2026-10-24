import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints081
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_081 (j : Fin 16) : upperValue ((point (16*81+j.val)+point ((16*81+j.val)+1))/2) ≤ payment (16*81+j.val) := by
  fin_cases j
  · change upperValue ((point (1296)+point ((1296)+1))/2) ≤ payment (1296)
    have hp : payment 1296 = (1375675847998:ℝ)/1000000000000 := rfl
    have hx : (point 1296+point 1297)/2 = (3891811:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1296
  · change upperValue ((point (1297)+point ((1297)+1))/2) ≤ payment (1297)
    have hp : payment 1297 = (1373558351278:ℝ)/1000000000000 := rfl
    have hx : (point 1297+point 1298)/2 = (1297955:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1297
  · change upperValue ((point (1298)+point ((1298)+1))/2) ≤ payment (1298)
    have hp : payment 1298 = (1371442150211:ℝ)/1000000000000 := rfl
    have hx : (point 1298+point 1299)/2 = (3895919:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1298
  · change upperValue ((point (1299)+point ((1299)+1))/2) ≤ payment (1299)
    have hp : payment 1299 = (1369327242003:ℝ)/1000000000000 := rfl
    have hx : (point 1299+point 1300)/2 = (3897973:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1299
  · change upperValue ((point (1300)+point ((1300)+1))/2) ≤ payment (1300)
    have hp : payment 1300 = (1367213623866:ℝ)/1000000000000 := rfl
    have hx : (point 1300+point 1301)/2 = (1300009:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1300
  · change upperValue ((point (1301)+point ((1301)+1))/2) ≤ payment (1301)
    have hp : payment 1301 = (1365101293015:ℝ)/1000000000000 := rfl
    have hx : (point 1301+point 1302)/2 = (3902081:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1301
  · change upperValue ((point (1302)+point ((1302)+1))/2) ≤ payment (1302)
    have hp : payment 1302 = (1362990246673:ℝ)/1000000000000 := rfl
    have hx : (point 1302+point 1303)/2 = (3904135:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1302
  · change upperValue ((point (1303)+point ((1303)+1))/2) ≤ payment (1303)
    have hp : payment 1303 = (1360880482065:ℝ)/1000000000000 := rfl
    have hx : (point 1303+point 1304)/2 = (1302063:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1303
  · change upperValue ((point (1304)+point ((1304)+1))/2) ≤ payment (1304)
    have hp : payment 1304 = (1358771996424:ℝ)/1000000000000 := rfl
    have hx : (point 1304+point 1305)/2 = (3908243:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1304
  · change upperValue ((point (1305)+point ((1305)+1))/2) ≤ payment (1305)
    have hp : payment 1305 = (1356664786985:ℝ)/1000000000000 := rfl
    have hx : (point 1305+point 1306)/2 = (3910297:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1305
  · change upperValue ((point (1306)+point ((1306)+1))/2) ≤ payment (1306)
    have hp : payment 1306 = (1354558850991:ℝ)/1000000000000 := rfl
    have hx : (point 1306+point 1307)/2 = (1304117:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1306
  · change upperValue ((point (1307)+point ((1307)+1))/2) ≤ payment (1307)
    have hp : payment 1307 = (1352454185688:ℝ)/1000000000000 := rfl
    have hx : (point 1307+point 1308)/2 = (3914405:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1307
  · change upperValue ((point (1308)+point ((1308)+1))/2) ≤ payment (1308)
    have hp : payment 1308 = (1350350788329:ℝ)/1000000000000 := rfl
    have hx : (point 1308+point 1309)/2 = (3916459:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1308
  · change upperValue ((point (1309)+point ((1309)+1))/2) ≤ payment (1309)
    have hp : payment 1309 = (1348248656169:ℝ)/1000000000000 := rfl
    have hx : (point 1309+point 1310)/2 = (1306171:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1309
  · change upperValue ((point (1310)+point ((1310)+1))/2) ≤ payment (1310)
    have hp : payment 1310 = (1346147786472:ℝ)/1000000000000 := rfl
    have hx : (point 1310+point 1311)/2 = (3920567:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1310
  · change upperValue ((point (1311)+point ((1311)+1))/2) ≤ payment (1311)
    have hp : payment 1311 = (1344048176503:ℝ)/1000000000000 := rfl
    have hx : (point 1311+point 1312)/2 = (3922621:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1311
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_081
