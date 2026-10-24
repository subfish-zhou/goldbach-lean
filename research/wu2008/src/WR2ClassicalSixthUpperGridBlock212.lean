import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints212
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_212 (j : Fin 16) : upperPayment (16*212+j.val) ≤
    upperValue ((point split endpoint 4096 (16*212+j.val)+point split endpoint 4096 (16*212+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3392 ≤ upperValue ((point split endpoint 4096 3392+point split endpoint 4096 3393)/2)
    have hp : upperPayment 3392 = (108729790510:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3392+point split endpoint 4096 3393)/2 = (661472927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661472927:ℝ)/168755200)*ClassicalSixthBranch.v ((661472927:ℝ)/168755200)/ClassicalSixthBranch.r = (86351668216145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3392
  · change upperPayment 3393 ≤ upperValue ((point split endpoint 4096 3393+point split endpoint 4096 3394)/2)
    have hp : upperPayment 3393 = (108588646426:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3393+point split endpoint 4096 3394)/2 = (661498077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661498077:ℝ)/168755200)*ClassicalSixthBranch.v ((661498077:ℝ)/168755200)/ClassicalSixthBranch.r = (86332518575577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3393
  · change upperPayment 3394 ≤ upperValue ((point split endpoint 4096 3394+point split endpoint 4096 3395)/2)
    have hp : upperPayment 3394 = (108447466451:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3394+point split endpoint 4096 3395)/2 = (661523227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661523227:ℝ)/168755200)*ClassicalSixthBranch.v ((661523227:ℝ)/168755200)/ClassicalSixthBranch.r = (86313370959081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3394
  · change upperPayment 3395 ≤ upperValue ((point split endpoint 4096 3395+point split endpoint 4096 3396)/2)
    have hp : upperPayment 3395 = (108306250576:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3395+point split endpoint 4096 3396)/2 = (661548377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661548377:ℝ)/168755200)*ClassicalSixthBranch.v ((661548377:ℝ)/168755200)/ClassicalSixthBranch.r = (86294225366657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3395
  · change upperPayment 3396 ≤ upperValue ((point split endpoint 4096 3396+point split endpoint 4096 3397)/2)
    have hp : upperPayment 3396 = (108164998793:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3396+point split endpoint 4096 3397)/2 = (661573527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661573527:ℝ)/168755200)*ClassicalSixthBranch.v ((661573527:ℝ)/168755200)/ClassicalSixthBranch.r = (86275081798305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3396
  · change upperPayment 3397 ≤ upperValue ((point split endpoint 4096 3397+point split endpoint 4096 3398)/2)
    have hp : upperPayment 3397 = (108023711092:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3397+point split endpoint 4096 3398)/2 = (661598677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661598677:ℝ)/168755200)*ClassicalSixthBranch.v ((661598677:ℝ)/168755200)/ClassicalSixthBranch.r = (86255940254025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3397
  · change upperPayment 3398 ≤ upperValue ((point split endpoint 4096 3398+point split endpoint 4096 3399)/2)
    have hp : upperPayment 3398 = (107882387463:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3398+point split endpoint 4096 3399)/2 = (661623827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661623827:ℝ)/168755200)*ClassicalSixthBranch.v ((661623827:ℝ)/168755200)/ClassicalSixthBranch.r = (86236800733817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3398
  · change upperPayment 3399 ≤ upperValue ((point split endpoint 4096 3399+point split endpoint 4096 3400)/2)
    have hp : upperPayment 3399 = (107741027899:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3399+point split endpoint 4096 3400)/2 = (661648977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661648977:ℝ)/168755200)*ClassicalSixthBranch.v ((661648977:ℝ)/168755200)/ClassicalSixthBranch.r = (86217663237681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3399
  · change upperPayment 3400 ≤ upperValue ((point split endpoint 4096 3400+point split endpoint 4096 3401)/2)
    have hp : upperPayment 3400 = (107599632390:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3400+point split endpoint 4096 3401)/2 = (661674127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661674127:ℝ)/168755200)*ClassicalSixthBranch.v ((661674127:ℝ)/168755200)/ClassicalSixthBranch.r = (86198527765617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3400
  · change upperPayment 3401 ≤ upperValue ((point split endpoint 4096 3401+point split endpoint 4096 3402)/2)
    have hp : upperPayment 3401 = (107458200926:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3401+point split endpoint 4096 3402)/2 = (661699277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661699277:ℝ)/168755200)*ClassicalSixthBranch.v ((661699277:ℝ)/168755200)/ClassicalSixthBranch.r = (86179394317625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3401
  · change upperPayment 3402 ≤ upperValue ((point split endpoint 4096 3402+point split endpoint 4096 3403)/2)
    have hp : upperPayment 3402 = (107316733498:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3402+point split endpoint 4096 3403)/2 = (6424509:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6424509:ℝ)/1638400)*ClassicalSixthBranch.v ((6424509:ℝ)/1638400)/ClassicalSixthBranch.r = (836507406735:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3402
  · change upperPayment 3403 ≤ upperValue ((point split endpoint 4096 3403+point split endpoint 4096 3404)/2)
    have hp : upperPayment 3403 = (107175230099:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3403+point split endpoint 4096 3404)/2 = (661749577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661749577:ℝ)/168755200)*ClassicalSixthBranch.v ((661749577:ℝ)/168755200)/ClassicalSixthBranch.r = (86141133493857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3403
  · change upperPayment 3404 ≤ upperValue ((point split endpoint 4096 3404+point split endpoint 4096 3405)/2)
    have hp : upperPayment 3404 = (107033690717:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3404+point split endpoint 4096 3405)/2 = (661774727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661774727:ℝ)/168755200)*ClassicalSixthBranch.v ((661774727:ℝ)/168755200)/ClassicalSixthBranch.r = (86122006118081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3404
  · change upperPayment 3405 ≤ upperValue ((point split endpoint 4096 3405+point split endpoint 4096 3406)/2)
    have hp : upperPayment 3405 = (106892115345:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3405+point split endpoint 4096 3406)/2 = (661799877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661799877:ℝ)/168755200)*ClassicalSixthBranch.v ((661799877:ℝ)/168755200)/ClassicalSixthBranch.r = (86102880766377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3405
  · change upperPayment 3406 ≤ upperValue ((point split endpoint 4096 3406+point split endpoint 4096 3407)/2)
    have hp : upperPayment 3406 = (106750503973:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3406+point split endpoint 4096 3407)/2 = (661825027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661825027:ℝ)/168755200)*ClassicalSixthBranch.v ((661825027:ℝ)/168755200)/ClassicalSixthBranch.r = (86083757438745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3406
  · change upperPayment 3407 ≤ upperValue ((point split endpoint 4096 3407+point split endpoint 4096 3408)/2)
    have hp : upperPayment 3407 = (106608856591:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3407+point split endpoint 4096 3408)/2 = (661850177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661850177:ℝ)/168755200)*ClassicalSixthBranch.v ((661850177:ℝ)/168755200)/ClassicalSixthBranch.r = (86064636135185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3407
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_212
