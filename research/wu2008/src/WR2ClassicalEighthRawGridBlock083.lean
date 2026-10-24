import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints083
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_083 (j : Fin 16) : upperValue ((point (16*83+j.val)+point ((16*83+j.val)+1))/2) ≤ payment (16*83+j.val) := by
  fin_cases j
  · change upperValue ((point (1328)+point ((1328)+1))/2) ≤ payment (1328)
    have hp : payment 1328 = (1308544920906:ℝ)/1000000000000 := rfl
    have hx : (point 1328+point 1329)/2 = (3957539:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1328
  · change upperValue ((point (1329)+point ((1329)+1))/2) ≤ payment (1329)
    have hp : payment 1329 = (1306467524277:ℝ)/1000000000000 := rfl
    have hx : (point 1329+point 1330)/2 = (3959593:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1329
  · change upperValue ((point (1330)+point ((1330)+1))/2) ≤ payment (1330)
    have hp : payment 1330 = (1304391336374:ℝ)/1000000000000 := rfl
    have hx : (point 1330+point 1331)/2 = (1320549:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1330
  · change upperValue ((point (1331)+point ((1331)+1))/2) ≤ payment (1331)
    have hp : payment 1331 = (1302316354562:ℝ)/1000000000000 := rfl
    have hx : (point 1331+point 1332)/2 = (3963701:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1331
  · change upperValue ((point (1332)+point ((1332)+1))/2) ≤ payment (1332)
    have hp : payment 1332 = (1300242576210:ℝ)/1000000000000 := rfl
    have hx : (point 1332+point 1333)/2 = (3965755:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1332
  · change upperValue ((point (1333)+point ((1333)+1))/2) ≤ payment (1333)
    have hp : payment 1333 = (1298169998689:ℝ)/1000000000000 := rfl
    have hx : (point 1333+point 1334)/2 = (1322603:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1333
  · change upperValue ((point (1334)+point ((1334)+1))/2) ≤ payment (1334)
    have hp : payment 1334 = (1296098619378:ℝ)/1000000000000 := rfl
    have hx : (point 1334+point 1335)/2 = (3969863:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1334
  · change upperValue ((point (1335)+point ((1335)+1))/2) ≤ payment (1335)
    have hp : payment 1335 = (1294028435660:ℝ)/1000000000000 := rfl
    have hx : (point 1335+point 1336)/2 = (3971917:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1335
  · change upperValue ((point (1336)+point ((1336)+1))/2) ≤ payment (1336)
    have hp : payment 1336 = (1291959444921:ℝ)/1000000000000 := rfl
    have hx : (point 1336+point 1337)/2 = (1324657:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1336
  · change upperValue ((point (1337)+point ((1337)+1))/2) ≤ payment (1337)
    have hp : payment 1337 = (1289891644553:ℝ)/1000000000000 := rfl
    have hx : (point 1337+point 1338)/2 = (3976025:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1337
  · change upperValue ((point (1338)+point ((1338)+1))/2) ≤ payment (1338)
    have hp : payment 1338 = (1287825031952:ℝ)/1000000000000 := rfl
    have hx : (point 1338+point 1339)/2 = (3978079:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1338
  · change upperValue ((point (1339)+point ((1339)+1))/2) ≤ payment (1339)
    have hp : payment 1339 = (1285759604520:ℝ)/1000000000000 := rfl
    have hx : (point 1339+point 1340)/2 = (1326711:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1339
  · change upperValue ((point (1340)+point ((1340)+1))/2) ≤ payment (1340)
    have hp : payment 1340 = (1283695359662:ℝ)/1000000000000 := rfl
    have hx : (point 1340+point 1341)/2 = (3982187:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1340
  · change upperValue ((point (1341)+point ((1341)+1))/2) ≤ payment (1341)
    have hp : payment 1341 = (1281632294787:ℝ)/1000000000000 := rfl
    have hx : (point 1341+point 1342)/2 = (3984241:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1341
  · change upperValue ((point (1342)+point ((1342)+1))/2) ≤ payment (1342)
    have hp : payment 1342 = (1279570407312:ℝ)/1000000000000 := rfl
    have hx : (point 1342+point 1343)/2 = (1328765:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1342
  · change upperValue ((point (1343)+point ((1343)+1))/2) ≤ payment (1343)
    have hp : payment 1343 = (1277509694654:ℝ)/1000000000000 := rfl
    have hx : (point 1343+point 1344)/2 = (3988349:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1343
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_083
