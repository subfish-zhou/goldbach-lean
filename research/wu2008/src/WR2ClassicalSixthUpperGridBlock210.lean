import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints210
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_210 (j : Fin 16) : upperPayment (16*210+j.val) ≤
    upperValue ((point split endpoint 4096 (16*210+j.val)+point split endpoint 4096 (16*210+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3360 ≤ upperValue ((point split endpoint 4096 3360+point split endpoint 4096 3361)/2)
    have hp : upperPayment 3360 = (113227505208:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3360+point split endpoint 4096 3361)/2 = (660668127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660668127:ℝ)/168755200)*ClassicalSixthBranch.v ((660668127:ℝ)/168755200)/ClassicalSixthBranch.r = (86965525424337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3360
  · change upperPayment 3361 ≤ upperValue ((point split endpoint 4096 3361+point split endpoint 4096 3362)/2)
    have hp : upperPayment 3361 = (113087504843:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3361+point split endpoint 4096 3362)/2 = (660693277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660693277:ℝ)/168755200)*ClassicalSixthBranch.v ((660693277:ℝ)/168755200)/ClassicalSixthBranch.r = (86946311013465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3361
  · change upperPayment 3362 ≤ upperValue ((point split endpoint 4096 3362+point split endpoint 4096 3363)/2)
    have hp : upperPayment 3362 = (112947468877:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3362+point split endpoint 4096 3363)/2 = (660718427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660718427:ℝ)/168755200)*ClassicalSixthBranch.v ((660718427:ℝ)/168755200)/ClassicalSixthBranch.r = (86927098626665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3362
  · change upperPayment 3363 ≤ upperValue ((point split endpoint 4096 3363+point split endpoint 4096 3364)/2)
    have hp : upperPayment 3363 = (112807397300:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3363+point split endpoint 4096 3364)/2 = (660743577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660743577:ℝ)/168755200)*ClassicalSixthBranch.v ((660743577:ℝ)/168755200)/ClassicalSixthBranch.r = (86907888263937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3363
  · change upperPayment 3364 ≤ upperValue ((point split endpoint 4096 3364+point split endpoint 4096 3365)/2)
    have hp : upperPayment 3364 = (112667290103:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3364+point split endpoint 4096 3365)/2 = (660768727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660768727:ℝ)/168755200)*ClassicalSixthBranch.v ((660768727:ℝ)/168755200)/ClassicalSixthBranch.r = (86888679925281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3364
  · change upperPayment 3365 ≤ upperValue ((point split endpoint 4096 3365+point split endpoint 4096 3366)/2)
    have hp : upperPayment 3365 = (112527147278:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3365+point split endpoint 4096 3366)/2 = (660793877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660793877:ℝ)/168755200)*ClassicalSixthBranch.v ((660793877:ℝ)/168755200)/ClassicalSixthBranch.r = (86869473610697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3365
  · change upperPayment 3366 ≤ upperValue ((point split endpoint 4096 3366+point split endpoint 4096 3367)/2)
    have hp : upperPayment 3366 = (112386968815:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3366+point split endpoint 4096 3367)/2 = (660819027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660819027:ℝ)/168755200)*ClassicalSixthBranch.v ((660819027:ℝ)/168755200)/ClassicalSixthBranch.r = (86850269320185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3366
  · change upperPayment 3367 ≤ upperValue ((point split endpoint 4096 3367+point split endpoint 4096 3368)/2)
    have hp : upperPayment 3367 = (112246754706:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3367+point split endpoint 4096 3368)/2 = (660844177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660844177:ℝ)/168755200)*ClassicalSixthBranch.v ((660844177:ℝ)/168755200)/ClassicalSixthBranch.r = (86831067053745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3367
  · change upperPayment 3368 ≤ upperValue ((point split endpoint 4096 3368+point split endpoint 4096 3369)/2)
    have hp : upperPayment 3368 = (112106504942:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3368+point split endpoint 4096 3369)/2 = (660869327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660869327:ℝ)/168755200)*ClassicalSixthBranch.v ((660869327:ℝ)/168755200)/ClassicalSixthBranch.r = (86811866811377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3368
  · change upperPayment 3369 ≤ upperValue ((point split endpoint 4096 3369+point split endpoint 4096 3370)/2)
    have hp : upperPayment 3369 = (111966219513:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3369+point split endpoint 4096 3370)/2 = (660894477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660894477:ℝ)/168755200)*ClassicalSixthBranch.v ((660894477:ℝ)/168755200)/ClassicalSixthBranch.r = (86792668593081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3369
  · change upperPayment 3370 ≤ upperValue ((point split endpoint 4096 3370+point split endpoint 4096 3371)/2)
    have hp : upperPayment 3370 = (111825898410:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3370+point split endpoint 4096 3371)/2 = (660919627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660919627:ℝ)/168755200)*ClassicalSixthBranch.v ((660919627:ℝ)/168755200)/ClassicalSixthBranch.r = (86773472398857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3370
  · change upperPayment 3371 ≤ upperValue ((point split endpoint 4096 3371+point split endpoint 4096 3372)/2)
    have hp : upperPayment 3371 = (111685541626:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3371+point split endpoint 4096 3372)/2 = (660944777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660944777:ℝ)/168755200)*ClassicalSixthBranch.v ((660944777:ℝ)/168755200)/ClassicalSixthBranch.r = (86754278228705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3371
  · change upperPayment 3372 ≤ upperValue ((point split endpoint 4096 3372+point split endpoint 4096 3373)/2)
    have hp : upperPayment 3372 = (111545149149:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3372+point split endpoint 4096 3373)/2 = (660969927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660969927:ℝ)/168755200)*ClassicalSixthBranch.v ((660969927:ℝ)/168755200)/ClassicalSixthBranch.r = (86735086082625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3372
  · change upperPayment 3373 ≤ upperValue ((point split endpoint 4096 3373+point split endpoint 4096 3374)/2)
    have hp : upperPayment 3373 = (111404720973:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3373+point split endpoint 4096 3374)/2 = (660995077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660995077:ℝ)/168755200)*ClassicalSixthBranch.v ((660995077:ℝ)/168755200)/ClassicalSixthBranch.r = (86715895960617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3373
  · change upperPayment 3374 ≤ upperValue ((point split endpoint 4096 3374+point split endpoint 4096 3375)/2)
    have hp : upperPayment 3374 = (111264257086:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3374+point split endpoint 4096 3375)/2 = (661020227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661020227:ℝ)/168755200)*ClassicalSixthBranch.v ((661020227:ℝ)/168755200)/ClassicalSixthBranch.r = (86696707862681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3374
  · change upperPayment 3375 ≤ upperValue ((point split endpoint 4096 3375+point split endpoint 4096 3376)/2)
    have hp : upperPayment 3375 = (111123757481:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3375+point split endpoint 4096 3376)/2 = (661045377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661045377:ℝ)/168755200)*ClassicalSixthBranch.v ((661045377:ℝ)/168755200)/ClassicalSixthBranch.r = (86677521788817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3375
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_210
