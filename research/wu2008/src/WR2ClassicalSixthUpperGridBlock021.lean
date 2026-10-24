import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints021
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_021 (j : Fin 16) : upperPayment (16*21+j.val) ≤
    upperValue ((point split endpoint 4096 (16*21+j.val)+point split endpoint 4096 (16*21+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 336 ≤ upperValue ((point split endpoint 4096 336+point split endpoint 4096 337)/2)
    have hp : upperPayment 336 = (405009144781:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 336+point split endpoint 4096 337)/2 = (584614527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584614527:ℝ)/168755200)*ClassicalSixthBranch.v ((584614527:ℝ)/168755200)/ClassicalSixthBranch.r = (1498326256455:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_336
  · change upperPayment 337 ≤ upperValue ((point split endpoint 4096 337+point split endpoint 4096 338)/2)
    have hp : upperPayment 337 = (404948467227:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 337+point split endpoint 4096 338)/2 = (584639677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584639677:ℝ)/168755200)*ClassicalSixthBranch.v ((584639677:ℝ)/168755200)/ClassicalSixthBranch.r = (154302269210265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_337
  · change upperPayment 338 ≤ upperValue ((point split endpoint 4096 338+point split endpoint 4096 339)/2)
    have hp : upperPayment 338 = (404887769650:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 338+point split endpoint 4096 339)/2 = (584664827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584664827:ℝ)/168755200)*ClassicalSixthBranch.v ((584664827:ℝ)/168755200)/ClassicalSixthBranch.r = (154276936029737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_338
  · change upperPayment 339 ≤ upperValue ((point split endpoint 4096 339+point split endpoint 4096 340)/2)
    have hp : upperPayment 339 = (404827052046:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 339+point split endpoint 4096 340)/2 = (584689977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584689977:ℝ)/168755200)*ClassicalSixthBranch.v ((584689977:ℝ)/168755200)/ClassicalSixthBranch.r = (154251604873281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_339
  · change upperPayment 340 ≤ upperValue ((point split endpoint 4096 340+point split endpoint 4096 341)/2)
    have hp : upperPayment 340 = (404766314415:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 340+point split endpoint 4096 341)/2 = (584715127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584715127:ℝ)/168755200)*ClassicalSixthBranch.v ((584715127:ℝ)/168755200)/ClassicalSixthBranch.r = (154226275740897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_340
  · change upperPayment 341 ≤ upperValue ((point split endpoint 4096 341+point split endpoint 4096 342)/2)
    have hp : upperPayment 341 = (404705556753:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 341+point split endpoint 4096 342)/2 = (584740277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584740277:ℝ)/168755200)*ClassicalSixthBranch.v ((584740277:ℝ)/168755200)/ClassicalSixthBranch.r = (154200948632585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_341
  · change upperPayment 342 ≤ upperValue ((point split endpoint 4096 342+point split endpoint 4096 343)/2)
    have hp : upperPayment 342 = (404644779058:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 342+point split endpoint 4096 343)/2 = (584765427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584765427:ℝ)/168755200)*ClassicalSixthBranch.v ((584765427:ℝ)/168755200)/ClassicalSixthBranch.r = (154175623548345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_342
  · change upperPayment 343 ≤ upperValue ((point split endpoint 4096 343+point split endpoint 4096 344)/2)
    have hp : upperPayment 343 = (404583981327:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 343+point split endpoint 4096 344)/2 = (584790577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584790577:ℝ)/168755200)*ClassicalSixthBranch.v ((584790577:ℝ)/168755200)/ClassicalSixthBranch.r = (154150300488177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_343
  · change upperPayment 344 ≤ upperValue ((point split endpoint 4096 344+point split endpoint 4096 345)/2)
    have hp : upperPayment 344 = (404523163557:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 344+point split endpoint 4096 345)/2 = (584815727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584815727:ℝ)/168755200)*ClassicalSixthBranch.v ((584815727:ℝ)/168755200)/ClassicalSixthBranch.r = (154124979452081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_344
  · change upperPayment 345 ≤ upperValue ((point split endpoint 4096 345+point split endpoint 4096 346)/2)
    have hp : upperPayment 345 = (404462325747:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 345+point split endpoint 4096 346)/2 = (584840877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584840877:ℝ)/168755200)*ClassicalSixthBranch.v ((584840877:ℝ)/168755200)/ClassicalSixthBranch.r = (154099660440057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_345
  · change upperPayment 346 ≤ upperValue ((point split endpoint 4096 346+point split endpoint 4096 347)/2)
    have hp : upperPayment 346 = (404401467894:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 346+point split endpoint 4096 347)/2 = (584866027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584866027:ℝ)/168755200)*ClassicalSixthBranch.v ((584866027:ℝ)/168755200)/ClassicalSixthBranch.r = (154074343452105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_346
  · change upperPayment 347 ≤ upperValue ((point split endpoint 4096 347+point split endpoint 4096 348)/2)
    have hp : upperPayment 347 = (404340589995:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 347+point split endpoint 4096 348)/2 = (584891177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584891177:ℝ)/168755200)*ClassicalSixthBranch.v ((584891177:ℝ)/168755200)/ClassicalSixthBranch.r = (154049028488225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_347
  · change upperPayment 348 ≤ upperValue ((point split endpoint 4096 348+point split endpoint 4096 349)/2)
    have hp : upperPayment 348 = (404279692047:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 348+point split endpoint 4096 349)/2 = (584916327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584916327:ℝ)/168755200)*ClassicalSixthBranch.v ((584916327:ℝ)/168755200)/ClassicalSixthBranch.r = (154023715548417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_348
  · change upperPayment 349 ≤ upperValue ((point split endpoint 4096 349+point split endpoint 4096 350)/2)
    have hp : upperPayment 349 = (404218774049:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 349+point split endpoint 4096 350)/2 = (584941477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584941477:ℝ)/168755200)*ClassicalSixthBranch.v ((584941477:ℝ)/168755200)/ClassicalSixthBranch.r = (153998404632681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_349
  · change upperPayment 350 ≤ upperValue ((point split endpoint 4096 350+point split endpoint 4096 351)/2)
    have hp : upperPayment 350 = (404157835997:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 350+point split endpoint 4096 351)/2 = (584966627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584966627:ℝ)/168755200)*ClassicalSixthBranch.v ((584966627:ℝ)/168755200)/ClassicalSixthBranch.r = (153973095741017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_350
  · change upperPayment 351 ≤ upperValue ((point split endpoint 4096 351+point split endpoint 4096 352)/2)
    have hp : upperPayment 351 = (404096877889:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 351+point split endpoint 4096 352)/2 = (584991777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584991777:ℝ)/168755200)*ClassicalSixthBranch.v ((584991777:ℝ)/168755200)/ClassicalSixthBranch.r = (153947788873425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_351
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_021
