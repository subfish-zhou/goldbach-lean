import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints214
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_214 (j : Fin 16) : upperPayment (16*214+j.val) ≤
    upperValue ((point split endpoint 4096 (16*214+j.val)+point split endpoint 4096 (16*214+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3424 ≤ upperValue ((point split endpoint 4096 3424+point split endpoint 4096 3425)/2)
    have hp : upperPayment 3424 = (104195332847:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3424+point split endpoint 4096 3425)/2 = (662277727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662277727:ℝ)/168755200)*ClassicalSixthBranch.v ((662277727:ℝ)/168755200)/ClassicalSixthBranch.r = (85739883657681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3424
  · change upperPayment 3425 ≤ upperValue ((point split endpoint 4096 3425+point split endpoint 4096 3426)/2)
    have hp : upperPayment 3425 = (104053035735:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3425+point split endpoint 4096 3426)/2 = (662302877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662302877:ℝ)/168755200)*ClassicalSixthBranch.v ((662302877:ℝ)/168755200)/ClassicalSixthBranch.r = (85720798787417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3425
  · change upperPayment 3426 ≤ upperValue ((point split endpoint 4096 3426+point split endpoint 4096 3427)/2)
    have hp : upperPayment 3426 = (103910702440:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3426+point split endpoint 4096 3427)/2 = (662328027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662328027:ℝ)/168755200)*ClassicalSixthBranch.v ((662328027:ℝ)/168755200)/ClassicalSixthBranch.r = (832055494575:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3426
  · change upperPayment 3427 ≤ upperValue ((point split endpoint 4096 3427+point split endpoint 4096 3428)/2)
    have hp : upperPayment 3427 = (103768332952:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3427+point split endpoint 4096 3428)/2 = (662353177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662353177:ℝ)/168755200)*ClassicalSixthBranch.v ((662353177:ℝ)/168755200)/ClassicalSixthBranch.r = (85682635119105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3427
  · change upperPayment 3428 ≤ upperValue ((point split endpoint 4096 3428+point split endpoint 4096 3429)/2)
    have hp : upperPayment 3428 = (103625927263:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3428+point split endpoint 4096 3429)/2 = (662378327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662378327:ℝ)/168755200)*ClassicalSixthBranch.v ((662378327:ℝ)/168755200)/ClassicalSixthBranch.r = (85663556321057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3428
  · change upperPayment 3429 ≤ upperValue ((point split endpoint 4096 3429+point split endpoint 4096 3430)/2)
    have hp : upperPayment 3429 = (103483485362:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3429+point split endpoint 4096 3430)/2 = (662403477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662403477:ℝ)/168755200)*ClassicalSixthBranch.v ((662403477:ℝ)/168755200)/ClassicalSixthBranch.r = (85644479547081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3429
  · change upperPayment 3430 ≤ upperValue ((point split endpoint 4096 3430+point split endpoint 4096 3431)/2)
    have hp : upperPayment 3430 = (103341007241:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3430+point split endpoint 4096 3431)/2 = (662428627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662428627:ℝ)/168755200)*ClassicalSixthBranch.v ((662428627:ℝ)/168755200)/ClassicalSixthBranch.r = (85625404797177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3430
  · change upperPayment 3431 ≤ upperValue ((point split endpoint 4096 3431+point split endpoint 4096 3432)/2)
    have hp : upperPayment 3431 = (103198492890:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3431+point split endpoint 4096 3432)/2 = (662453777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662453777:ℝ)/168755200)*ClassicalSixthBranch.v ((662453777:ℝ)/168755200)/ClassicalSixthBranch.r = (85606332071345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3431
  · change upperPayment 3432 ≤ upperValue ((point split endpoint 4096 3432+point split endpoint 4096 3433)/2)
    have hp : upperPayment 3432 = (103055942301:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3432+point split endpoint 4096 3433)/2 = (662478927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662478927:ℝ)/168755200)*ClassicalSixthBranch.v ((662478927:ℝ)/168755200)/ClassicalSixthBranch.r = (64496805855:ℝ)/55297703936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3432
  · change upperPayment 3433 ≤ upperValue ((point split endpoint 4096 3433+point split endpoint 4096 3434)/2)
    have hp : upperPayment 3433 = (102913355463:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3433+point split endpoint 4096 3434)/2 = (662504077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662504077:ℝ)/168755200)*ClassicalSixthBranch.v ((662504077:ℝ)/168755200)/ClassicalSixthBranch.r = (85568192691897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3433
  · change upperPayment 3434 ≤ upperValue ((point split endpoint 4096 3434+point split endpoint 4096 3435)/2)
    have hp : upperPayment 3434 = (102770732369:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3434+point split endpoint 4096 3435)/2 = (662529227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662529227:ℝ)/168755200)*ClassicalSixthBranch.v ((662529227:ℝ)/168755200)/ClassicalSixthBranch.r = (85549126038281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3434
  · change upperPayment 3435 ≤ upperValue ((point split endpoint 4096 3435+point split endpoint 4096 3436)/2)
    have hp : upperPayment 3435 = (102628073008:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3435+point split endpoint 4096 3436)/2 = (662554377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662554377:ℝ)/168755200)*ClassicalSixthBranch.v ((662554377:ℝ)/168755200)/ClassicalSixthBranch.r = (85530061408737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3435
  · change upperPayment 3436 ≤ upperValue ((point split endpoint 4096 3436+point split endpoint 4096 3437)/2)
    have hp : upperPayment 3436 = (102485377371:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3436+point split endpoint 4096 3437)/2 = (662579527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662579527:ℝ)/168755200)*ClassicalSixthBranch.v ((662579527:ℝ)/168755200)/ClassicalSixthBranch.r = (85510998803265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3436
  · change upperPayment 3437 ≤ upperValue ((point split endpoint 4096 3437+point split endpoint 4096 3438)/2)
    have hp : upperPayment 3437 = (102342645449:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3437+point split endpoint 4096 3438)/2 = (662604677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662604677:ℝ)/168755200)*ClassicalSixthBranch.v ((662604677:ℝ)/168755200)/ClassicalSixthBranch.r = (85491938221865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3437
  · change upperPayment 3438 ≤ upperValue ((point split endpoint 4096 3438+point split endpoint 4096 3439)/2)
    have hp : upperPayment 3438 = (102199877233:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3438+point split endpoint 4096 3439)/2 = (662629827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662629827:ℝ)/168755200)*ClassicalSixthBranch.v ((662629827:ℝ)/168755200)/ClassicalSixthBranch.r = (85472879664537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3438
  · change upperPayment 3439 ≤ upperValue ((point split endpoint 4096 3439+point split endpoint 4096 3440)/2)
    have hp : upperPayment 3439 = (102057072713:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3439+point split endpoint 4096 3440)/2 = (662654977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662654977:ℝ)/168755200)*ClassicalSixthBranch.v ((662654977:ℝ)/168755200)/ClassicalSixthBranch.r = (85453823131281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3439
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_214
