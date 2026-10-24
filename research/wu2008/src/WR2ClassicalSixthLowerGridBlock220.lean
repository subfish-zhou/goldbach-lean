import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints220
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_220 (j : Fin 16) : lowerPayment (16*220+j.val) ≤
    lowerValue ((point 2 split 4096 (16*220+j.val)+point 2 split 4096 (16*220+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3520 ≤ lowerValue ((point 2 split 4096 3520+point 2 split 4096 3521)/2)
    have hp : lowerPayment 3520 = (368280900888:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3520+point 2 split 4096 3521)/2 = (542621771:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542621771:ℝ)/168755200)/ClassicalSixthBranch.v ((542621771:ℝ)/168755200) = (541832387387:ℝ)/251566689944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3520
  · change lowerPayment 3521 ≤ lowerValue ((point 2 split 4096 3521+point 2 split 4096 3522)/2)
    have hp : lowerPayment 3521 = (368373806755:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3521+point 2 split 4096 3522)/2 = (542680033:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542680033:ℝ)/168755200)/ClassicalSixthBranch.v ((542680033:ℝ)/168755200) = (541755073713:ℝ)/251518682056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3521
  · change lowerPayment 3522 ≤ lowerValue ((point 2 split 4096 3522+point 2 split 4096 3523)/2)
    have hp : lowerPayment 3522 = (368466724950:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3522+point 2 split 4096 3523)/2 = (108547659:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108547659:ℝ)/33751040)/ClassicalSixthBranch.v ((108547659:ℝ)/33751040) = (541677760039:ℝ)/251470674168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3522
  · change lowerPayment 3523 ≤ lowerValue ((point 2 split 4096 3523+point 2 split 4096 3524)/2)
    have hp : lowerPayment 3523 = (368559655490:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3523+point 2 split 4096 3524)/2 = (542796557:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542796557:ℝ)/168755200)/ClassicalSixthBranch.v ((542796557:ℝ)/168755200) = (108320089273:ℝ)/50284533256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3523
  · change lowerPayment 3524 ≤ lowerValue ((point 2 split 4096 3524+point 2 split 4096 3525)/2)
    have hp : lowerPayment 3524 = (368652598390:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3524+point 2 split 4096 3525)/2 = (542854819:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542854819:ℝ)/168755200)/ClassicalSixthBranch.v ((542854819:ℝ)/168755200) = (541523132691:ℝ)/251374658392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3524
  · change lowerPayment 3525 ≤ lowerValue ((point 2 split 4096 3525+point 2 split 4096 3526)/2)
    have hp : lowerPayment 3525 = (368745553666:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3525+point 2 split 4096 3526)/2 = (542913081:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542913081:ℝ)/168755200)/ClassicalSixthBranch.v ((542913081:ℝ)/168755200) = (541445819017:ℝ)/251326650504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3525
  · change lowerPayment 3526 ≤ lowerValue ((point 2 split 4096 3526+point 2 split 4096 3527)/2)
    have hp : lowerPayment 3526 = (368838521333:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3526+point 2 split 4096 3527)/2 = (542971343:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((542971343:ℝ)/168755200)/ClassicalSixthBranch.v ((542971343:ℝ)/168755200) = (541368505343:ℝ)/251278642616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3526
  · change lowerPayment 3527 ≤ lowerValue ((point 2 split 4096 3527+point 2 split 4096 3528)/2)
    have hp : lowerPayment 3527 = (368931501407:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3527+point 2 split 4096 3528)/2 = (108605921:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108605921:ℝ)/33751040)/ClassicalSixthBranch.v ((108605921:ℝ)/33751040) = (541291191669:ℝ)/251230634728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3527
  · change lowerPayment 3528 ≤ lowerValue ((point 2 split 4096 3528+point 2 split 4096 3529)/2)
    have hp : lowerPayment 3528 = (369024493903:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3528+point 2 split 4096 3529)/2 = (543087867:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543087867:ℝ)/168755200)/ClassicalSixthBranch.v ((543087867:ℝ)/168755200) = (108242775599:ℝ)/50236525368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3528
  · change lowerPayment 3529 ≤ lowerValue ((point 2 split 4096 3529+point 2 split 4096 3530)/2)
    have hp : lowerPayment 3529 = (369117498838:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3529+point 2 split 4096 3530)/2 = (543146129:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543146129:ℝ)/168755200)/ClassicalSixthBranch.v ((543146129:ℝ)/168755200) = (541136564321:ℝ)/251134618952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3529
  · change lowerPayment 3530 ≤ lowerValue ((point 2 split 4096 3530+point 2 split 4096 3531)/2)
    have hp : lowerPayment 3530 = (369210516226:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3530+point 2 split 4096 3531)/2 = (543204391:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543204391:ℝ)/168755200)/ClassicalSixthBranch.v ((543204391:ℝ)/168755200) = (541059250647:ℝ)/251086611064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3530
  · change lowerPayment 3531 ≤ lowerValue ((point 2 split 4096 3531+point 2 split 4096 3532)/2)
    have hp : lowerPayment 3531 = (369303546084:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3531+point 2 split 4096 3532)/2 = (543262653:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543262653:ℝ)/168755200)/ClassicalSixthBranch.v ((543262653:ℝ)/168755200) = (540981936973:ℝ)/251038603176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3531
  · change lowerPayment 3532 ≤ lowerValue ((point 2 split 4096 3532+point 2 split 4096 3533)/2)
    have hp : lowerPayment 3532 = (369396588427:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3532+point 2 split 4096 3533)/2 = (108664183:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108664183:ℝ)/33751040)/ClassicalSixthBranch.v ((108664183:ℝ)/33751040) = (540904623299:ℝ)/250990595288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3532
  · change lowerPayment 3533 ≤ lowerValue ((point 2 split 4096 3533+point 2 split 4096 3534)/2)
    have hp : lowerPayment 3533 = (369489643270:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3533+point 2 split 4096 3534)/2 = (543379177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543379177:ℝ)/168755200)/ClassicalSixthBranch.v ((543379177:ℝ)/168755200) = (21633092385:ℝ)/10037703496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3533
  · change lowerPayment 3534 ≤ lowerValue ((point 2 split 4096 3534+point 2 split 4096 3535)/2)
    have hp : lowerPayment 3534 = (369582710631:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3534+point 2 split 4096 3535)/2 = (543437439:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543437439:ℝ)/168755200)/ClassicalSixthBranch.v ((543437439:ℝ)/168755200) = (540749995951:ℝ)/250894579512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3534
  · change lowerPayment 3535 ≤ lowerValue ((point 2 split 4096 3535+point 2 split 4096 3536)/2)
    have hp : lowerPayment 3535 = (369675790523:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3535+point 2 split 4096 3536)/2 = (543495701:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543495701:ℝ)/168755200)/ClassicalSixthBranch.v ((543495701:ℝ)/168755200) = (540672682277:ℝ)/250846571624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3535
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_220
