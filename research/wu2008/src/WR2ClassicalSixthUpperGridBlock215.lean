import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints215
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_215 (j : Fin 16) : upperPayment (16*215+j.val) ≤
    upperValue ((point split endpoint 4096 (16*215+j.val)+point split endpoint 4096 (16*215+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3440 ≤ upperValue ((point split endpoint 4096 3440+point split endpoint 4096 3441)/2)
    have hp : upperPayment 3440 = (101914231881:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3440+point split endpoint 4096 3441)/2 = (662680127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662680127:ℝ)/168755200)*ClassicalSixthBranch.v ((662680127:ℝ)/168755200)/ClassicalSixthBranch.r = (85434768622097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3440
  · change upperPayment 3441 ≤ upperValue ((point split endpoint 4096 3441+point split endpoint 4096 3442)/2)
    have hp : upperPayment 3441 = (101771354726:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3441+point split endpoint 4096 3442)/2 = (662705277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662705277:ℝ)/168755200)*ClassicalSixthBranch.v ((662705277:ℝ)/168755200)/ClassicalSixthBranch.r = (85415716136985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3441
  · change upperPayment 3442 ≤ upperValue ((point split endpoint 4096 3442+point split endpoint 4096 3443)/2)
    have hp : upperPayment 3442 = (101628441240:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3442+point split endpoint 4096 3443)/2 = (662730427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662730427:ℝ)/168755200)*ClassicalSixthBranch.v ((662730427:ℝ)/168755200)/ClassicalSixthBranch.r = (85396665675945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3442
  · change upperPayment 3443 ≤ upperValue ((point split endpoint 4096 3443+point split endpoint 4096 3444)/2)
    have hp : upperPayment 3443 = (101485491414:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3443+point split endpoint 4096 3444)/2 = (662755577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662755577:ℝ)/168755200)*ClassicalSixthBranch.v ((662755577:ℝ)/168755200)/ClassicalSixthBranch.r = (85377617238977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3443
  · change upperPayment 3444 ≤ upperValue ((point split endpoint 4096 3444+point split endpoint 4096 3445)/2)
    have hp : upperPayment 3444 = (101342505238:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3444+point split endpoint 4096 3445)/2 = (662780727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662780727:ℝ)/168755200)*ClassicalSixthBranch.v ((662780727:ℝ)/168755200)/ClassicalSixthBranch.r = (85358570826081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3444
  · change upperPayment 3445 ≤ upperValue ((point split endpoint 4096 3445+point split endpoint 4096 3446)/2)
    have hp : upperPayment 3445 = (101199482702:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3445+point split endpoint 4096 3446)/2 = (662805877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662805877:ℝ)/168755200)*ClassicalSixthBranch.v ((662805877:ℝ)/168755200)/ClassicalSixthBranch.r = (85339526437257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3445
  · change upperPayment 3446 ≤ upperValue ((point split endpoint 4096 3446+point split endpoint 4096 3447)/2)
    have hp : upperPayment 3446 = (101056423798:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3446+point split endpoint 4096 3447)/2 = (662831027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662831027:ℝ)/168755200)*ClassicalSixthBranch.v ((662831027:ℝ)/168755200)/ClassicalSixthBranch.r = (85320484072505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3446
  · change upperPayment 3447 ≤ upperValue ((point split endpoint 4096 3447+point split endpoint 4096 3448)/2)
    have hp : upperPayment 3447 = (100913328517:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3447+point split endpoint 4096 3448)/2 = (662856177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662856177:ℝ)/168755200)*ClassicalSixthBranch.v ((662856177:ℝ)/168755200)/ClassicalSixthBranch.r = (85301443731825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3447
  · change upperPayment 3448 ≤ upperValue ((point split endpoint 4096 3448+point split endpoint 4096 3449)/2)
    have hp : upperPayment 3448 = (100770196848:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3448+point split endpoint 4096 3449)/2 = (662881327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662881327:ℝ)/168755200)*ClassicalSixthBranch.v ((662881327:ℝ)/168755200)/ClassicalSixthBranch.r = (85282405415217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3448
  · change upperPayment 3449 ≤ upperValue ((point split endpoint 4096 3449+point split endpoint 4096 3450)/2)
    have hp : upperPayment 3449 = (100627028783:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3449+point split endpoint 4096 3450)/2 = (662906477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662906477:ℝ)/168755200)*ClassicalSixthBranch.v ((662906477:ℝ)/168755200)/ClassicalSixthBranch.r = (85263369122681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3449
  · change upperPayment 3450 ≤ upperValue ((point split endpoint 4096 3450+point split endpoint 4096 3451)/2)
    have hp : upperPayment 3450 = (100483824312:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3450+point split endpoint 4096 3451)/2 = (662931627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662931627:ℝ)/168755200)*ClassicalSixthBranch.v ((662931627:ℝ)/168755200)/ClassicalSixthBranch.r = (85244334854217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3450
  · change upperPayment 3451 ≤ upperValue ((point split endpoint 4096 3451+point split endpoint 4096 3452)/2)
    have hp : upperPayment 3451 = (100340583426:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3451+point split endpoint 4096 3452)/2 = (662956777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662956777:ℝ)/168755200)*ClassicalSixthBranch.v ((662956777:ℝ)/168755200)/ClassicalSixthBranch.r = (85225302609825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3451
  · change upperPayment 3452 ≤ upperValue ((point split endpoint 4096 3452+point split endpoint 4096 3453)/2)
    have hp : upperPayment 3452 = (100197306117:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3452+point split endpoint 4096 3453)/2 = (662981927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662981927:ℝ)/168755200)*ClassicalSixthBranch.v ((662981927:ℝ)/168755200)/ClassicalSixthBranch.r = (85206272389505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3452
  · change upperPayment 3453 ≤ upperValue ((point split endpoint 4096 3453+point split endpoint 4096 3454)/2)
    have hp : upperPayment 3453 = (100053992373:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3453+point split endpoint 4096 3454)/2 = (663007077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663007077:ℝ)/168755200)*ClassicalSixthBranch.v ((663007077:ℝ)/168755200)/ClassicalSixthBranch.r = (85187244193257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3453
  · change upperPayment 3454 ≤ upperValue ((point split endpoint 4096 3454+point split endpoint 4096 3455)/2)
    have hp : upperPayment 3454 = (99910642187:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3454+point split endpoint 4096 3455)/2 = (663032227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663032227:ℝ)/168755200)*ClassicalSixthBranch.v ((663032227:ℝ)/168755200)/ClassicalSixthBranch.r = (85168218021081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3454
  · change upperPayment 3455 ≤ upperValue ((point split endpoint 4096 3455+point split endpoint 4096 3456)/2)
    have hp : upperPayment 3455 = (99767255548:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3455+point split endpoint 4096 3456)/2 = (663057377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663057377:ℝ)/168755200)*ClassicalSixthBranch.v ((663057377:ℝ)/168755200)/ClassicalSixthBranch.r = (85149193872977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3455
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_215
