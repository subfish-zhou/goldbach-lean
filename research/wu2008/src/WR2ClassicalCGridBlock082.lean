import WR2ClassicalCPayments
import WR2ClassicalCPoints082
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_082 (j : Fin 16) : cPayment (16*82+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*82+j.val)+point (1327/200) 4096 (16*82+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1312 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1312+point (1327/200) 4096 1313)/2)
    have hp : cPayment 1312 = (82294012685:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1312+point (1327/200) 4096 1313)/2 = (186407:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1312
  · change cPayment 1313 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1313+point (1327/200) 4096 1314)/2)
    have hp : cPayment 1313 = (82286256390:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1313+point (1327/200) 4096 1314)/2 = (4661229:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1313
  · change cPayment 1314 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1314+point (1327/200) 4096 1315)/2)
    have hp : cPayment 1314 = (82278452295:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1314+point (1327/200) 4096 1315)/2 = (4662283:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1314
  · change cPayment 1315 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1315+point (1327/200) 4096 1316)/2)
    have hp : cPayment 1315 = (82270600473:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1315+point (1327/200) 4096 1316)/2 = (4663337:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1315
  · change cPayment 1316 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1316+point (1327/200) 4096 1317)/2)
    have hp : cPayment 1316 = (82262700997:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1316+point (1327/200) 4096 1317)/2 = (4664391:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1316
  · change cPayment 1317 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1317+point (1327/200) 4096 1318)/2)
    have hp : cPayment 1317 = (82254753941:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1317+point (1327/200) 4096 1318)/2 = (933089:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1317
  · change cPayment 1318 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1318+point (1327/200) 4096 1319)/2)
    have hp : cPayment 1318 = (82246759379:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1318+point (1327/200) 4096 1319)/2 = (4666499:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1318
  · change cPayment 1319 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1319+point (1327/200) 4096 1320)/2)
    have hp : cPayment 1319 = (82238717382:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1319+point (1327/200) 4096 1320)/2 = (4667553:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1319
  · change cPayment 1320 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1320+point (1327/200) 4096 1321)/2)
    have hp : cPayment 1320 = (82230628024:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1320+point (1327/200) 4096 1321)/2 = (4668607:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1320
  · change cPayment 1321 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1321+point (1327/200) 4096 1322)/2)
    have hp : cPayment 1321 = (82222491378:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1321+point (1327/200) 4096 1322)/2 = (4669661:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1321
  · change cPayment 1322 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1322+point (1327/200) 4096 1323)/2)
    have hp : cPayment 1322 = (82214307517:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1322+point (1327/200) 4096 1323)/2 = (934143:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1322
  · change cPayment 1323 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1323+point (1327/200) 4096 1324)/2)
    have hp : cPayment 1323 = (82206076512:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1323+point (1327/200) 4096 1324)/2 = (4671769:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1323
  · change cPayment 1324 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1324+point (1327/200) 4096 1325)/2)
    have hp : cPayment 1324 = (82197798438:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1324+point (1327/200) 4096 1325)/2 = (4672823:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1324
  · change cPayment 1325 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1325+point (1327/200) 4096 1326)/2)
    have hp : cPayment 1325 = (82189473365:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1325+point (1327/200) 4096 1326)/2 = (4673877:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1325
  · change cPayment 1326 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1326+point (1327/200) 4096 1327)/2)
    have hp : cPayment 1326 = (82181101367:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1326+point (1327/200) 4096 1327)/2 = (4674931:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1326
  · change cPayment 1327 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1327+point (1327/200) 4096 1328)/2)
    have hp : cPayment 1327 = (82172682516:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1327+point (1327/200) 4096 1328)/2 = (935197:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1327
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_082
