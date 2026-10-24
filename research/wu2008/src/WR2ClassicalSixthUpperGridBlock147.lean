import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints147
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_147 (j : Fin 16) : upperPayment (16*147+j.val) ≤
    upperValue ((point split endpoint 4096 (16*147+j.val)+point split endpoint 4096 (16*147+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2352 ≤ upperValue ((point split endpoint 4096 2352+point split endpoint 4096 2353)/2)
    have hp : upperPayment 2352 = (237632988485:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2352+point split endpoint 4096 2353)/2 = (635316927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635316927:ℝ)/168755200)*ClassicalSixthBranch.v ((635316927:ℝ)/168755200)/ClassicalSixthBranch.r = (107362965061905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2352
  · change upperPayment 2353 ≤ upperValue ((point split endpoint 4096 2353+point split endpoint 4096 2354)/2)
    have hp : upperPayment 2353 = (237524878689:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2353+point split endpoint 4096 2354)/2 = (635342077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635342077:ℝ)/168755200)*ClassicalSixthBranch.v ((635342077:ℝ)/168755200)/ClassicalSixthBranch.r = (107341710386457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2353
  · change upperPayment 2354 ≤ upperValue ((point split endpoint 4096 2354+point split endpoint 4096 2355)/2)
    have hp : upperPayment 2354 = (237416740708:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2354+point split endpoint 4096 2355)/2 = (635367227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635367227:ℝ)/168755200)*ClassicalSixthBranch.v ((635367227:ℝ)/168755200)/ClassicalSixthBranch.r = (107320457735081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2354
  · change upperPayment 2355 ≤ upperValue ((point split endpoint 4096 2355+point split endpoint 4096 2356)/2)
    have hp : upperPayment 2355 = (237308574539:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2355+point split endpoint 4096 2356)/2 = (635392377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635392377:ℝ)/168755200)*ClassicalSixthBranch.v ((635392377:ℝ)/168755200)/ClassicalSixthBranch.r = (107299207107777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2355
  · change upperPayment 2356 ≤ upperValue ((point split endpoint 4096 2356+point split endpoint 4096 2357)/2)
    have hp : upperPayment 2356 = (237200380173:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2356+point split endpoint 4096 2357)/2 = (635417527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635417527:ℝ)/168755200)*ClassicalSixthBranch.v ((635417527:ℝ)/168755200)/ClassicalSixthBranch.r = (107277958504545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2356
  · change upperPayment 2357 ≤ upperValue ((point split endpoint 4096 2357+point split endpoint 4096 2358)/2)
    have hp : upperPayment 2357 = (237092157606:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2357+point split endpoint 4096 2358)/2 = (635442677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635442677:ℝ)/168755200)*ClassicalSixthBranch.v ((635442677:ℝ)/168755200)/ClassicalSixthBranch.r = (107256711925385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2357
  · change upperPayment 2358 ≤ upperValue ((point split endpoint 4096 2358+point split endpoint 4096 2359)/2)
    have hp : upperPayment 2358 = (236983906831:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2358+point split endpoint 4096 2359)/2 = (635467827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635467827:ℝ)/168755200)*ClassicalSixthBranch.v ((635467827:ℝ)/168755200)/ClassicalSixthBranch.r = (107235467370297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2358
  · change upperPayment 2359 ≤ upperValue ((point split endpoint 4096 2359+point split endpoint 4096 2360)/2)
    have hp : upperPayment 2359 = (236875627842:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2359+point split endpoint 4096 2360)/2 = (635492977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635492977:ℝ)/168755200)*ClassicalSixthBranch.v ((635492977:ℝ)/168755200)/ClassicalSixthBranch.r = (107214224839281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2359
  · change upperPayment 2360 ≤ upperValue ((point split endpoint 4096 2360+point split endpoint 4096 2361)/2)
    have hp : upperPayment 2360 = (236767320634:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2360+point split endpoint 4096 2361)/2 = (635518127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635518127:ℝ)/168755200)*ClassicalSixthBranch.v ((635518127:ℝ)/168755200)/ClassicalSixthBranch.r = (107192984332337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2360
  · change upperPayment 2361 ≤ upperValue ((point split endpoint 4096 2361+point split endpoint 4096 2362)/2)
    have hp : upperPayment 2361 = (236658985200:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2361+point split endpoint 4096 2362)/2 = (635543277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635543277:ℝ)/168755200)*ClassicalSixthBranch.v ((635543277:ℝ)/168755200)/ClassicalSixthBranch.r = (107171745849465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2361
  · change upperPayment 2362 ≤ upperValue ((point split endpoint 4096 2362+point split endpoint 4096 2363)/2)
    have hp : upperPayment 2362 = (236550621535:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2362+point split endpoint 4096 2363)/2 = (635568427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635568427:ℝ)/168755200)*ClassicalSixthBranch.v ((635568427:ℝ)/168755200)/ClassicalSixthBranch.r = (107150509390665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2362
  · change upperPayment 2363 ≤ upperValue ((point split endpoint 4096 2363+point split endpoint 4096 2364)/2)
    have hp : upperPayment 2363 = (236442229633:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2363+point split endpoint 4096 2364)/2 = (635593577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635593577:ℝ)/168755200)*ClassicalSixthBranch.v ((635593577:ℝ)/168755200)/ClassicalSixthBranch.r = (107129274955937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2363
  · change upperPayment 2364 ≤ upperValue ((point split endpoint 4096 2364+point split endpoint 4096 2365)/2)
    have hp : upperPayment 2364 = (236333809486:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2364+point split endpoint 4096 2365)/2 = (635618727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635618727:ℝ)/168755200)*ClassicalSixthBranch.v ((635618727:ℝ)/168755200)/ClassicalSixthBranch.r = (107108042545281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2364
  · change upperPayment 2365 ≤ upperValue ((point split endpoint 4096 2365+point split endpoint 4096 2366)/2)
    have hp : upperPayment 2365 = (236225361091:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2365+point split endpoint 4096 2366)/2 = (635643877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635643877:ℝ)/168755200)*ClassicalSixthBranch.v ((635643877:ℝ)/168755200)/ClassicalSixthBranch.r = (107086812158697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2365
  · change upperPayment 2366 ≤ upperValue ((point split endpoint 4096 2366+point split endpoint 4096 2367)/2)
    have hp : upperPayment 2366 = (236116884439:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2366+point split endpoint 4096 2367)/2 = (635669027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635669027:ℝ)/168755200)*ClassicalSixthBranch.v ((635669027:ℝ)/168755200)/ClassicalSixthBranch.r = (107065583796185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2366
  · change upperPayment 2367 ≤ upperValue ((point split endpoint 4096 2367+point split endpoint 4096 2368)/2)
    have hp : upperPayment 2367 = (236008379527:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2367+point split endpoint 4096 2368)/2 = (635694177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635694177:ℝ)/168755200)*ClassicalSixthBranch.v ((635694177:ℝ)/168755200)/ClassicalSixthBranch.r = (107044357457745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2367
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_147
