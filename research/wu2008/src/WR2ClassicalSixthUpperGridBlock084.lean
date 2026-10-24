import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints084
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_084 (j : Fin 16) : upperPayment (16*84+j.val) ≤
    upperValue ((point split endpoint 4096 (16*84+j.val)+point split endpoint 4096 (16*84+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1344 ≤ upperValue ((point split endpoint 4096 1344+point split endpoint 4096 1345)/2)
    have hp : upperPayment 1344 = (333200590520:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1344+point split endpoint 4096 1345)/2 = (609965727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609965727:ℝ)/168755200)*ClassicalSixthBranch.v ((609965727:ℝ)/168755200)/ClassicalSixthBranch.r = (129816991392081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1344
  · change upperPayment 1345 ≤ upperValue ((point split endpoint 4096 1345+point split endpoint 4096 1346)/2)
    have hp : upperPayment 1345 = (333118229170:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1345+point split endpoint 4096 1346)/2 = (609990877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609990877:ℝ)/168755200)*ClassicalSixthBranch.v ((609990877:ℝ)/168755200)/ClassicalSixthBranch.r = (129793696452057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1345
  · change upperPayment 1346 ≤ upperValue ((point split endpoint 4096 1346+point split endpoint 4096 1347)/2)
    have hp : upperPayment 1346 = (333035844575:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1346+point split endpoint 4096 1347)/2 = (610016027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610016027:ℝ)/168755200)*ClassicalSixthBranch.v ((610016027:ℝ)/168755200)/ClassicalSixthBranch.r = (129770403536105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1346
  · change upperPayment 1347 ≤ upperValue ((point split endpoint 4096 1347+point split endpoint 4096 1348)/2)
    have hp : upperPayment 1347 = (332953436729:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1347+point split endpoint 4096 1348)/2 = (610041177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610041177:ℝ)/168755200)*ClassicalSixthBranch.v ((610041177:ℝ)/168755200)/ClassicalSixthBranch.r = (129747112644225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1347
  · change upperPayment 1348 ≤ upperValue ((point split endpoint 4096 1348+point split endpoint 4096 1349)/2)
    have hp : upperPayment 1348 = (332871005630:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1348+point split endpoint 4096 1349)/2 = (610066327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610066327:ℝ)/168755200)*ClassicalSixthBranch.v ((610066327:ℝ)/168755200)/ClassicalSixthBranch.r = (129723823776417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1348
  · change upperPayment 1349 ≤ upperValue ((point split endpoint 4096 1349+point split endpoint 4096 1350)/2)
    have hp : upperPayment 1349 = (332788551273:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1349+point split endpoint 4096 1350)/2 = (610091477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610091477:ℝ)/168755200)*ClassicalSixthBranch.v ((610091477:ℝ)/168755200)/ClassicalSixthBranch.r = (129700536932681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1349
  · change upperPayment 1350 ≤ upperValue ((point split endpoint 4096 1350+point split endpoint 4096 1351)/2)
    have hp : upperPayment 1350 = (332706073655:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1350+point split endpoint 4096 1351)/2 = (610116627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610116627:ℝ)/168755200)*ClassicalSixthBranch.v ((610116627:ℝ)/168755200)/ClassicalSixthBranch.r = (129677252113017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1350
  · change upperPayment 1351 ≤ upperValue ((point split endpoint 4096 1351+point split endpoint 4096 1352)/2)
    have hp : upperPayment 1351 = (332623572771:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1351+point split endpoint 4096 1352)/2 = (610141777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610141777:ℝ)/168755200)*ClassicalSixthBranch.v ((610141777:ℝ)/168755200)/ClassicalSixthBranch.r = (129653969317425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1351
  · change upperPayment 1352 ≤ upperValue ((point split endpoint 4096 1352+point split endpoint 4096 1353)/2)
    have hp : upperPayment 1352 = (332541048618:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1352+point split endpoint 4096 1353)/2 = (610166927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610166927:ℝ)/168755200)*ClassicalSixthBranch.v ((610166927:ℝ)/168755200)/ClassicalSixthBranch.r = (129630688545905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1352
  · change upperPayment 1353 ≤ upperValue ((point split endpoint 4096 1353+point split endpoint 4096 1354)/2)
    have hp : upperPayment 1353 = (332458501191:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1353+point split endpoint 4096 1354)/2 = (610192077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610192077:ℝ)/168755200)*ClassicalSixthBranch.v ((610192077:ℝ)/168755200)/ClassicalSixthBranch.r = (129607409798457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1353
  · change upperPayment 1354 ≤ upperValue ((point split endpoint 4096 1354+point split endpoint 4096 1355)/2)
    have hp : upperPayment 1354 = (332375930486:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1354+point split endpoint 4096 1355)/2 = (610217227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610217227:ℝ)/168755200)*ClassicalSixthBranch.v ((610217227:ℝ)/168755200)/ClassicalSixthBranch.r = (129584133075081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1354
  · change upperPayment 1355 ≤ upperValue ((point split endpoint 4096 1355+point split endpoint 4096 1356)/2)
    have hp : upperPayment 1355 = (332293336500:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1355+point split endpoint 4096 1356)/2 = (610242377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610242377:ℝ)/168755200)*ClassicalSixthBranch.v ((610242377:ℝ)/168755200)/ClassicalSixthBranch.r = (129560858375777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1355
  · change upperPayment 1356 ≤ upperValue ((point split endpoint 4096 1356+point split endpoint 4096 1357)/2)
    have hp : upperPayment 1356 = (332210719229:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1356+point split endpoint 4096 1357)/2 = (610267527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610267527:ℝ)/168755200)*ClassicalSixthBranch.v ((610267527:ℝ)/168755200)/ClassicalSixthBranch.r = (129537585700545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1356
  · change upperPayment 1357 ≤ upperValue ((point split endpoint 4096 1357+point split endpoint 4096 1358)/2)
    have hp : upperPayment 1357 = (332128078668:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1357+point split endpoint 4096 1358)/2 = (610292677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610292677:ℝ)/168755200)*ClassicalSixthBranch.v ((610292677:ℝ)/168755200)/ClassicalSixthBranch.r = (129514315049385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1357
  · change upperPayment 1358 ≤ upperValue ((point split endpoint 4096 1358+point split endpoint 4096 1359)/2)
    have hp : upperPayment 1358 = (332045414814:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1358+point split endpoint 4096 1359)/2 = (610317827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610317827:ℝ)/168755200)*ClassicalSixthBranch.v ((610317827:ℝ)/168755200)/ClassicalSixthBranch.r = (129491046422297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1358
  · change upperPayment 1359 ≤ upperValue ((point split endpoint 4096 1359+point split endpoint 4096 1360)/2)
    have hp : upperPayment 1359 = (331962727662:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1359+point split endpoint 4096 1360)/2 = (610342977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610342977:ℝ)/168755200)*ClassicalSixthBranch.v ((610342977:ℝ)/168755200)/ClassicalSixthBranch.r = (129467779819281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1359
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_084
