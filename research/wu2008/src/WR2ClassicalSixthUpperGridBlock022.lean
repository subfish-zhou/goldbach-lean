import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints022
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_022 (j : Fin 16) : upperPayment (16*22+j.val) ≤
    upperValue ((point split endpoint 4096 (16*22+j.val)+point split endpoint 4096 (16*22+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 352 ≤ upperValue ((point split endpoint 4096 352+point split endpoint 4096 353)/2)
    have hp : upperPayment 352 = (404035899723:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 352+point split endpoint 4096 353)/2 = (585016927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585016927:ℝ)/168755200)*ClassicalSixthBranch.v ((585016927:ℝ)/168755200)/ClassicalSixthBranch.r = (153922484029905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_352
  · change upperPayment 353 ≤ upperValue ((point split endpoint 4096 353+point split endpoint 4096 354)/2)
    have hp : upperPayment 353 = (403974901495:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 353+point split endpoint 4096 354)/2 = (585042077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585042077:ℝ)/168755200)*ClassicalSixthBranch.v ((585042077:ℝ)/168755200)/ClassicalSixthBranch.r = (153897181210457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_353
  · change upperPayment 354 ≤ upperValue ((point split endpoint 4096 354+point split endpoint 4096 355)/2)
    have hp : upperPayment 354 = (403913883205:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 354+point split endpoint 4096 355)/2 = (585067227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585067227:ℝ)/168755200)*ClassicalSixthBranch.v ((585067227:ℝ)/168755200)/ClassicalSixthBranch.r = (153871880415081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_354
  · change upperPayment 355 ≤ upperValue ((point split endpoint 4096 355+point split endpoint 4096 356)/2)
    have hp : upperPayment 355 = (403852844848:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 355+point split endpoint 4096 356)/2 = (585092377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585092377:ℝ)/168755200)*ClassicalSixthBranch.v ((585092377:ℝ)/168755200)/ClassicalSixthBranch.r = (153846581643777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_355
  · change upperPayment 356 ≤ upperValue ((point split endpoint 4096 356+point split endpoint 4096 357)/2)
    have hp : upperPayment 356 = (403791786423:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 356+point split endpoint 4096 357)/2 = (585117527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585117527:ℝ)/168755200)*ClassicalSixthBranch.v ((585117527:ℝ)/168755200)/ClassicalSixthBranch.r = (153821284896545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_356
  · change upperPayment 357 ≤ upperValue ((point split endpoint 4096 357+point split endpoint 4096 358)/2)
    have hp : upperPayment 357 = (403730707926:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 357+point split endpoint 4096 358)/2 = (585142677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585142677:ℝ)/168755200)*ClassicalSixthBranch.v ((585142677:ℝ)/168755200)/ClassicalSixthBranch.r = (153795990173385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_357
  · change upperPayment 358 ≤ upperValue ((point split endpoint 4096 358+point split endpoint 4096 359)/2)
    have hp : upperPayment 358 = (403669609356:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 358+point split endpoint 4096 359)/2 = (585167827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585167827:ℝ)/168755200)*ClassicalSixthBranch.v ((585167827:ℝ)/168755200)/ClassicalSixthBranch.r = (153770697474297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_358
  · change upperPayment 359 ≤ upperValue ((point split endpoint 4096 359+point split endpoint 4096 360)/2)
    have hp : upperPayment 359 = (403608490710:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 359+point split endpoint 4096 360)/2 = (585192977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585192977:ℝ)/168755200)*ClassicalSixthBranch.v ((585192977:ℝ)/168755200)/ClassicalSixthBranch.r = (153745406799281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_359
  · change upperPayment 360 ≤ upperValue ((point split endpoint 4096 360+point split endpoint 4096 361)/2)
    have hp : upperPayment 360 = (403547351986:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 360+point split endpoint 4096 361)/2 = (585218127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585218127:ℝ)/168755200)*ClassicalSixthBranch.v ((585218127:ℝ)/168755200)/ClassicalSixthBranch.r = (153720118148337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_360
  · change upperPayment 361 ≤ upperValue ((point split endpoint 4096 361+point split endpoint 4096 362)/2)
    have hp : upperPayment 361 = (403486193180:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 361+point split endpoint 4096 362)/2 = (585243277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585243277:ℝ)/168755200)*ClassicalSixthBranch.v ((585243277:ℝ)/168755200)/ClassicalSixthBranch.r = (153694831521465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_361
  · change upperPayment 362 ≤ upperValue ((point split endpoint 4096 362+point split endpoint 4096 363)/2)
    have hp : upperPayment 362 = (403425014290:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 362+point split endpoint 4096 363)/2 = (585268427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585268427:ℝ)/168755200)*ClassicalSixthBranch.v ((585268427:ℝ)/168755200)/ClassicalSixthBranch.r = (153669546918665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_362
  · change upperPayment 363 ≤ upperValue ((point split endpoint 4096 363+point split endpoint 4096 364)/2)
    have hp : upperPayment 363 = (403363815314:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 363+point split endpoint 4096 364)/2 = (585293577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585293577:ℝ)/168755200)*ClassicalSixthBranch.v ((585293577:ℝ)/168755200)/ClassicalSixthBranch.r = (153644264339937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_363
  · change upperPayment 364 ≤ upperValue ((point split endpoint 4096 364+point split endpoint 4096 365)/2)
    have hp : upperPayment 364 = (403302596249:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 364+point split endpoint 4096 365)/2 = (585318727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585318727:ℝ)/168755200)*ClassicalSixthBranch.v ((585318727:ℝ)/168755200)/ClassicalSixthBranch.r = (153618983785281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_364
  · change upperPayment 365 ≤ upperValue ((point split endpoint 4096 365+point split endpoint 4096 366)/2)
    have hp : upperPayment 365 = (403241357092:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 365+point split endpoint 4096 366)/2 = (585343877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585343877:ℝ)/168755200)*ClassicalSixthBranch.v ((585343877:ℝ)/168755200)/ClassicalSixthBranch.r = (153593705254697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_365
  · change upperPayment 366 ≤ upperValue ((point split endpoint 4096 366+point split endpoint 4096 367)/2)
    have hp : upperPayment 366 = (403180097842:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 366+point split endpoint 4096 367)/2 = (585369027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585369027:ℝ)/168755200)*ClassicalSixthBranch.v ((585369027:ℝ)/168755200)/ClassicalSixthBranch.r = (153568428748185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_366
  · change upperPayment 367 ≤ upperValue ((point split endpoint 4096 367+point split endpoint 4096 368)/2)
    have hp : upperPayment 367 = (403118818495:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 367+point split endpoint 4096 368)/2 = (585394177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((585394177:ℝ)/168755200)*ClassicalSixthBranch.v ((585394177:ℝ)/168755200)/ClassicalSixthBranch.r = (153543154265745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_367
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_022
