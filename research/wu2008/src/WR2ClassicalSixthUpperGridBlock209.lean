import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints209
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_209 (j : Fin 16) : upperPayment (16*209+j.val) ≤
    upperValue ((point split endpoint 4096 (16*209+j.val)+point split endpoint 4096 (16*209+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3344 ≤ upperValue ((point split endpoint 4096 3344+point split endpoint 4096 3345)/2)
    have hp : upperPayment 3344 = (115462676543:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3344+point split endpoint 4096 3345)/2 = (660265727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660265727:ℝ)/168755200)*ClassicalSixthBranch.v ((660265727:ℝ)/168755200)/ClassicalSixthBranch.r = (87273231272081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3344
  · change upperPayment 3345 ≤ upperValue ((point split endpoint 4096 3345+point split endpoint 4096 3346)/2)
    have hp : upperPayment 3345 = (115323244586:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3345+point split endpoint 4096 3346)/2 = (660290877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660290877:ℝ)/168755200)*ClassicalSixthBranch.v ((660290877:ℝ)/168755200)/ClassicalSixthBranch.r = (87253984476057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3345
  · change upperPayment 3346 ≤ upperValue ((point split endpoint 4096 3346+point split endpoint 4096 3347)/2)
    have hp : upperPayment 3346 = (115183777170:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3346+point split endpoint 4096 3347)/2 = (660316027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660316027:ℝ)/168755200)*ClassicalSixthBranch.v ((660316027:ℝ)/168755200)/ClassicalSixthBranch.r = (87234739704105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3346
  · change upperPayment 3347 ≤ upperValue ((point split endpoint 4096 3347+point split endpoint 4096 3348)/2)
    have hp : upperPayment 3347 = (115044274287:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3347+point split endpoint 4096 3348)/2 = (660341177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660341177:ℝ)/168755200)*ClassicalSixthBranch.v ((660341177:ℝ)/168755200)/ClassicalSixthBranch.r = (87215496956225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3347
  · change upperPayment 3348 ≤ upperValue ((point split endpoint 4096 3348+point split endpoint 4096 3349)/2)
    have hp : upperPayment 3348 = (114904735927:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3348+point split endpoint 4096 3349)/2 = (660366327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660366327:ℝ)/168755200)*ClassicalSixthBranch.v ((660366327:ℝ)/168755200)/ClassicalSixthBranch.r = (87196256232417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3348
  · change upperPayment 3349 ≤ upperValue ((point split endpoint 4096 3349+point split endpoint 4096 3350)/2)
    have hp : upperPayment 3349 = (114765162082:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3349+point split endpoint 4096 3350)/2 = (660391477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660391477:ℝ)/168755200)*ClassicalSixthBranch.v ((660391477:ℝ)/168755200)/ClassicalSixthBranch.r = (87177017532681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3349
  · change upperPayment 3350 ≤ upperValue ((point split endpoint 4096 3350+point split endpoint 4096 3351)/2)
    have hp : upperPayment 3350 = (114625552743:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3350+point split endpoint 4096 3351)/2 = (660416627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660416627:ℝ)/168755200)*ClassicalSixthBranch.v ((660416627:ℝ)/168755200)/ClassicalSixthBranch.r = (87157780857017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3350
  · change upperPayment 3351 ≤ upperValue ((point split endpoint 4096 3351+point split endpoint 4096 3352)/2)
    have hp : upperPayment 3351 = (114485907901:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3351+point split endpoint 4096 3352)/2 = (660441777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660441777:ℝ)/168755200)*ClassicalSixthBranch.v ((660441777:ℝ)/168755200)/ClassicalSixthBranch.r = (87138546205425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3351
  · change upperPayment 3352 ≤ upperValue ((point split endpoint 4096 3352+point split endpoint 4096 3353)/2)
    have hp : upperPayment 3352 = (114346227547:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3352+point split endpoint 4096 3353)/2 = (660466927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660466927:ℝ)/168755200)*ClassicalSixthBranch.v ((660466927:ℝ)/168755200)/ClassicalSixthBranch.r = (87119313577905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3352
  · change upperPayment 3353 ≤ upperValue ((point split endpoint 4096 3353+point split endpoint 4096 3354)/2)
    have hp : upperPayment 3353 = (114206511672:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3353+point split endpoint 4096 3354)/2 = (660492077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660492077:ℝ)/168755200)*ClassicalSixthBranch.v ((660492077:ℝ)/168755200)/ClassicalSixthBranch.r = (87100082974457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3353
  · change upperPayment 3354 ≤ upperValue ((point split endpoint 4096 3354+point split endpoint 4096 3355)/2)
    have hp : upperPayment 3354 = (114066760267:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3354+point split endpoint 4096 3355)/2 = (660517227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660517227:ℝ)/168755200)*ClassicalSixthBranch.v ((660517227:ℝ)/168755200)/ClassicalSixthBranch.r = (87080854395081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3354
  · change upperPayment 3355 ≤ upperValue ((point split endpoint 4096 3355+point split endpoint 4096 3356)/2)
    have hp : upperPayment 3355 = (113926973323:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3355+point split endpoint 4096 3356)/2 = (660542377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660542377:ℝ)/168755200)*ClassicalSixthBranch.v ((660542377:ℝ)/168755200)/ClassicalSixthBranch.r = (87061627839777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3355
  · change upperPayment 3356 ≤ upperValue ((point split endpoint 4096 3356+point split endpoint 4096 3357)/2)
    have hp : upperPayment 3356 = (113787150832:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3356+point split endpoint 4096 3357)/2 = (660567527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660567527:ℝ)/168755200)*ClassicalSixthBranch.v ((660567527:ℝ)/168755200)/ClassicalSixthBranch.r = (87042403308545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3356
  · change upperPayment 3357 ≤ upperValue ((point split endpoint 4096 3357+point split endpoint 4096 3358)/2)
    have hp : upperPayment 3357 = (113647292783:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3357+point split endpoint 4096 3358)/2 = (660592677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660592677:ℝ)/168755200)*ClassicalSixthBranch.v ((660592677:ℝ)/168755200)/ClassicalSixthBranch.r = (87023180801385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3357
  · change upperPayment 3358 ≤ upperValue ((point split endpoint 4096 3358+point split endpoint 4096 3359)/2)
    have hp : upperPayment 3358 = (113507399169:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3358+point split endpoint 4096 3359)/2 = (660617827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660617827:ℝ)/168755200)*ClassicalSixthBranch.v ((660617827:ℝ)/168755200)/ClassicalSixthBranch.r = (87003960318297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3358
  · change upperPayment 3359 ≤ upperValue ((point split endpoint 4096 3359+point split endpoint 4096 3360)/2)
    have hp : upperPayment 3359 = (113367469980:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3359+point split endpoint 4096 3360)/2 = (660642977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660642977:ℝ)/168755200)*ClassicalSixthBranch.v ((660642977:ℝ)/168755200)/ClassicalSixthBranch.r = (86984741859281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3359
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_209
