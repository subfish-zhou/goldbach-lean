import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints217
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_217 (j : Fin 16) : upperPayment (16*217+j.val) ≤
    upperValue ((point split endpoint 4096 (16*217+j.val)+point split endpoint 4096 (16*217+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3472 ≤ upperValue ((point split endpoint 4096 3472+point split endpoint 4096 3473)/2)
    have hp : upperPayment 3472 = (97324096453:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3472+point split endpoint 4096 3473)/2 = (663484927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663484927:ℝ)/168755200)*ClassicalSixthBranch.v ((663484927:ℝ)/168755200)/ClassicalSixthBranch.r = (84826093038225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3472
  · change upperPayment 3473 ≤ upperValue ((point split endpoint 4096 3473+point split endpoint 4096 3474)/2)
    have hp : upperPayment 3473 = (97180052076:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3473+point split endpoint 4096 3474)/2 = (663510077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663510077:ℝ)/168755200)*ClassicalSixthBranch.v ((663510077:ℝ)/168755200)/ClassicalSixthBranch.r = (84807105323417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3473
  · change upperPayment 3474 ≤ upperValue ((point split endpoint 4096 3474+point split endpoint 4096 3475)/2)
    have hp : upperPayment 3474 = (97035971069:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3474+point split endpoint 4096 3475)/2 = (663535227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663535227:ℝ)/168755200)*ClassicalSixthBranch.v ((663535227:ℝ)/168755200)/ClassicalSixthBranch.r = (84788119632681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3474
  · change upperPayment 3475 ≤ upperValue ((point split endpoint 4096 3475+point split endpoint 4096 3476)/2)
    have hp : upperPayment 3475 = (96891853422:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3475+point split endpoint 4096 3476)/2 = (663560377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663560377:ℝ)/168755200)*ClassicalSixthBranch.v ((663560377:ℝ)/168755200)/ClassicalSixthBranch.r = (84769135966017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3475
  · change upperPayment 3476 ≤ upperValue ((point split endpoint 4096 3476+point split endpoint 4096 3477)/2)
    have hp : upperPayment 3476 = (96747699127:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3476+point split endpoint 4096 3477)/2 = (663585527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663585527:ℝ)/168755200)*ClassicalSixthBranch.v ((663585527:ℝ)/168755200)/ClassicalSixthBranch.r = (84750154323425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3476
  · change upperPayment 3477 ≤ upperValue ((point split endpoint 4096 3477+point split endpoint 4096 3478)/2)
    have hp : upperPayment 3477 = (96603508173:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3477+point split endpoint 4096 3478)/2 = (663610677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663610677:ℝ)/168755200)*ClassicalSixthBranch.v ((663610677:ℝ)/168755200)/ClassicalSixthBranch.r = (84731174704905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3477
  · change upperPayment 3478 ≤ upperValue ((point split endpoint 4096 3478+point split endpoint 4096 3479)/2)
    have hp : upperPayment 3478 = (96459280552:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3478+point split endpoint 4096 3479)/2 = (663635827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663635827:ℝ)/168755200)*ClassicalSixthBranch.v ((663635827:ℝ)/168755200)/ClassicalSixthBranch.r = (84712197110457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3478
  · change upperPayment 3479 ≤ upperValue ((point split endpoint 4096 3479+point split endpoint 4096 3480)/2)
    have hp : upperPayment 3479 = (96315016254:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3479+point split endpoint 4096 3480)/2 = (663660977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663660977:ℝ)/168755200)*ClassicalSixthBranch.v ((663660977:ℝ)/168755200)/ClassicalSixthBranch.r = (84693221540081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3479
  · change upperPayment 3480 ≤ upperValue ((point split endpoint 4096 3480+point split endpoint 4096 3481)/2)
    have hp : upperPayment 3480 = (96170715269:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3480+point split endpoint 4096 3481)/2 = (663686127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663686127:ℝ)/168755200)*ClassicalSixthBranch.v ((663686127:ℝ)/168755200)/ClassicalSixthBranch.r = (84674247993777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3480
  · change upperPayment 3481 ≤ upperValue ((point split endpoint 4096 3481+point split endpoint 4096 3482)/2)
    have hp : upperPayment 3481 = (96026377588:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3481+point split endpoint 4096 3482)/2 = (663711277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663711277:ℝ)/168755200)*ClassicalSixthBranch.v ((663711277:ℝ)/168755200)/ClassicalSixthBranch.r = (84655276471545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3481
  · change upperPayment 3482 ≤ upperValue ((point split endpoint 4096 3482+point split endpoint 4096 3483)/2)
    have hp : upperPayment 3482 = (95882003202:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3482+point split endpoint 4096 3483)/2 = (663736427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663736427:ℝ)/168755200)*ClassicalSixthBranch.v ((663736427:ℝ)/168755200)/ClassicalSixthBranch.r = (84636306973385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3482
  · change upperPayment 3483 ≤ upperValue ((point split endpoint 4096 3483+point split endpoint 4096 3484)/2)
    have hp : upperPayment 3483 = (95737592101:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3483+point split endpoint 4096 3484)/2 = (663761577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663761577:ℝ)/168755200)*ClassicalSixthBranch.v ((663761577:ℝ)/168755200)/ClassicalSixthBranch.r = (84617339499297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3483
  · change upperPayment 3484 ≤ upperValue ((point split endpoint 4096 3484+point split endpoint 4096 3485)/2)
    have hp : upperPayment 3484 = (95593144275:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3484+point split endpoint 4096 3485)/2 = (663786727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663786727:ℝ)/168755200)*ClassicalSixthBranch.v ((663786727:ℝ)/168755200)/ClassicalSixthBranch.r = (84598374049281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3484
  · change upperPayment 3485 ≤ upperValue ((point split endpoint 4096 3485+point split endpoint 4096 3486)/2)
    have hp : upperPayment 3485 = (95448659716:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3485+point split endpoint 4096 3486)/2 = (663811877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663811877:ℝ)/168755200)*ClassicalSixthBranch.v ((663811877:ℝ)/168755200)/ClassicalSixthBranch.r = (84579410623337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3485
  · change upperPayment 3486 ≤ upperValue ((point split endpoint 4096 3486+point split endpoint 4096 3487)/2)
    have hp : upperPayment 3486 = (95304138414:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3486+point split endpoint 4096 3487)/2 = (663837027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663837027:ℝ)/168755200)*ClassicalSixthBranch.v ((663837027:ℝ)/168755200)/ClassicalSixthBranch.r = (84560449221465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3486
  · change upperPayment 3487 ≤ upperValue ((point split endpoint 4096 3487+point split endpoint 4096 3488)/2)
    have hp : upperPayment 3487 = (95159580360:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3487+point split endpoint 4096 3488)/2 = (663862177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663862177:ℝ)/168755200)*ClassicalSixthBranch.v ((663862177:ℝ)/168755200)/ClassicalSixthBranch.r = (84541489843665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3487
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_217
