import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints213
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_213 (j : Fin 16) : upperPayment (16*213+j.val) ≤
    upperValue ((point split endpoint 4096 (16*213+j.val)+point split endpoint 4096 (16*213+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3408 ≤ upperValue ((point split endpoint 4096 3408+point split endpoint 4096 3409)/2)
    have hp : upperPayment 3408 = (106467173192:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3408+point split endpoint 4096 3409)/2 = (661875327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661875327:ℝ)/168755200)*ClassicalSixthBranch.v ((661875327:ℝ)/168755200)/ClassicalSixthBranch.r = (86045516855697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3408
  · change upperPayment 3409 ≤ upperValue ((point split endpoint 4096 3409+point split endpoint 4096 3410)/2)
    have hp : upperPayment 3409 = (106325453765:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3409+point split endpoint 4096 3410)/2 = (661900477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661900477:ℝ)/168755200)*ClassicalSixthBranch.v ((661900477:ℝ)/168755200)/ClassicalSixthBranch.r = (86026399600281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3409
  · change upperPayment 3410 ≤ upperValue ((point split endpoint 4096 3410+point split endpoint 4096 3411)/2)
    have hp : upperPayment 3410 = (106183698302:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3410+point split endpoint 4096 3411)/2 = (661925627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661925627:ℝ)/168755200)*ClassicalSixthBranch.v ((661925627:ℝ)/168755200)/ClassicalSixthBranch.r = (86007284368937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3410
  · change upperPayment 3411 ≤ upperValue ((point split endpoint 4096 3411+point split endpoint 4096 3412)/2)
    have hp : upperPayment 3411 = (106041906793:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3411+point split endpoint 4096 3412)/2 = (661950777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661950777:ℝ)/168755200)*ClassicalSixthBranch.v ((661950777:ℝ)/168755200)/ClassicalSixthBranch.r = (85988171161665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3411
  · change upperPayment 3412 ≤ upperValue ((point split endpoint 4096 3412+point split endpoint 4096 3413)/2)
    have hp : upperPayment 3412 = (105900079229:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3412+point split endpoint 4096 3413)/2 = (661975927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661975927:ℝ)/168755200)*ClassicalSixthBranch.v ((661975927:ℝ)/168755200)/ClassicalSixthBranch.r = (85969059978465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3412
  · change upperPayment 3413 ≤ upperValue ((point split endpoint 4096 3413+point split endpoint 4096 3414)/2)
    have hp : upperPayment 3413 = (105758215601:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3413+point split endpoint 4096 3414)/2 = (662001077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662001077:ℝ)/168755200)*ClassicalSixthBranch.v ((662001077:ℝ)/168755200)/ClassicalSixthBranch.r = (85949950819337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3413
  · change upperPayment 3414 ≤ upperValue ((point split endpoint 4096 3414+point split endpoint 4096 3415)/2)
    have hp : upperPayment 3414 = (105616315900:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3414+point split endpoint 4096 3415)/2 = (662026227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662026227:ℝ)/168755200)*ClassicalSixthBranch.v ((662026227:ℝ)/168755200)/ClassicalSixthBranch.r = (85930843684281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3414
  · change upperPayment 3415 ≤ upperValue ((point split endpoint 4096 3415+point split endpoint 4096 3416)/2)
    have hp : upperPayment 3415 = (105474380116:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3415+point split endpoint 4096 3416)/2 = (662051377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662051377:ℝ)/168755200)*ClassicalSixthBranch.v ((662051377:ℝ)/168755200)/ClassicalSixthBranch.r = (85911738573297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3415
  · change upperPayment 3416 ≤ upperValue ((point split endpoint 4096 3416+point split endpoint 4096 3417)/2)
    have hp : upperPayment 3416 = (105332408242:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3416+point split endpoint 4096 3417)/2 = (662076527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662076527:ℝ)/168755200)*ClassicalSixthBranch.v ((662076527:ℝ)/168755200)/ClassicalSixthBranch.r = (85892635486385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3416
  · change upperPayment 3417 ≤ upperValue ((point split endpoint 4096 3417+point split endpoint 4096 3418)/2)
    have hp : upperPayment 3417 = (105190400266:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3417+point split endpoint 4096 3418)/2 = (662101677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662101677:ℝ)/168755200)*ClassicalSixthBranch.v ((662101677:ℝ)/168755200)/ClassicalSixthBranch.r = (85873534423545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3417
  · change upperPayment 3418 ≤ upperValue ((point split endpoint 4096 3418+point split endpoint 4096 3419)/2)
    have hp : upperPayment 3418 = (105048356181:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3418+point split endpoint 4096 3419)/2 = (662126827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662126827:ℝ)/168755200)*ClassicalSixthBranch.v ((662126827:ℝ)/168755200)/ClassicalSixthBranch.r = (85854435384777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3418
  · change upperPayment 3419 ≤ upperValue ((point split endpoint 4096 3419+point split endpoint 4096 3420)/2)
    have hp : upperPayment 3419 = (104906275976:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3419+point split endpoint 4096 3420)/2 = (662151977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662151977:ℝ)/168755200)*ClassicalSixthBranch.v ((662151977:ℝ)/168755200)/ClassicalSixthBranch.r = (85835338370081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3419
  · change upperPayment 3420 ≤ upperValue ((point split endpoint 4096 3420+point split endpoint 4096 3421)/2)
    have hp : upperPayment 3420 = (104764159644:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3420+point split endpoint 4096 3421)/2 = (662177127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662177127:ℝ)/168755200)*ClassicalSixthBranch.v ((662177127:ℝ)/168755200)/ClassicalSixthBranch.r = (85816243379457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3420
  · change upperPayment 3421 ≤ upperValue ((point split endpoint 4096 3421+point split endpoint 4096 3422)/2)
    have hp : upperPayment 3421 = (104622007174:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3421+point split endpoint 4096 3422)/2 = (662202277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662202277:ℝ)/168755200)*ClassicalSixthBranch.v ((662202277:ℝ)/168755200)/ClassicalSixthBranch.r = (85797150412905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3421
  · change upperPayment 3422 ≤ upperValue ((point split endpoint 4096 3422+point split endpoint 4096 3423)/2)
    have hp : upperPayment 3422 = (104479818557:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3422+point split endpoint 4096 3423)/2 = (662227427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662227427:ℝ)/168755200)*ClassicalSixthBranch.v ((662227427:ℝ)/168755200)/ClassicalSixthBranch.r = (85778059470425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3422
  · change upperPayment 3423 ≤ upperValue ((point split endpoint 4096 3423+point split endpoint 4096 3424)/2)
    have hp : upperPayment 3423 = (104337593784:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3423+point split endpoint 4096 3424)/2 = (662252577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((662252577:ℝ)/168755200)*ClassicalSixthBranch.v ((662252577:ℝ)/168755200)/ClassicalSixthBranch.r = (85758970552017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3423
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_213
