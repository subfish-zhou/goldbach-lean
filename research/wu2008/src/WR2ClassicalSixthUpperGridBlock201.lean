import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints201
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_201 (j : Fin 16) : upperPayment (16*201+j.val) ≤
    upperValue ((point split endpoint 4096 (16*201+j.val)+point split endpoint 4096 (16*201+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3216 ≤ upperValue ((point split endpoint 4096 3216+point split endpoint 4096 3217)/2)
    have hp : upperPayment 3216 = (133020368598:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3216+point split endpoint 4096 3217)/2 = (657046527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657046527:ℝ)/168755200)*ClassicalSixthBranch.v ((657046527:ℝ)/168755200)/ClassicalSixthBranch.r = (89753531901585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3216
  · change upperPayment 3217 ≤ upperValue ((point split endpoint 4096 3217+point split endpoint 4096 3218)/2)
    have hp : upperPayment 3217 = (132885403023:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3217+point split endpoint 4096 3218)/2 = (657071677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657071677:ℝ)/168755200)*ClassicalSixthBranch.v ((657071677:ℝ)/168755200)/ClassicalSixthBranch.r = (89734026024345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3217
  · change upperPayment 3218 ≤ upperValue ((point split endpoint 4096 3218+point split endpoint 4096 3219)/2)
    have hp : upperPayment 3218 = (132750403101:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3218+point split endpoint 4096 3219)/2 = (657096827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657096827:ℝ)/168755200)*ClassicalSixthBranch.v ((657096827:ℝ)/168755200)/ClassicalSixthBranch.r = (89714522171177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3218
  · change upperPayment 3219 ≤ upperValue ((point split endpoint 4096 3219+point split endpoint 4096 3220)/2)
    have hp : upperPayment 3219 = (132615368823:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3219+point split endpoint 4096 3220)/2 = (657121977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657121977:ℝ)/168755200)*ClassicalSixthBranch.v ((657121977:ℝ)/168755200)/ClassicalSixthBranch.r = (89695020342081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3219
  · change upperPayment 3220 ≤ upperValue ((point split endpoint 4096 3220+point split endpoint 4096 3221)/2)
    have hp : upperPayment 3220 = (132480300181:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3220+point split endpoint 4096 3221)/2 = (657147127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657147127:ℝ)/168755200)*ClassicalSixthBranch.v ((657147127:ℝ)/168755200)/ClassicalSixthBranch.r = (870636121719:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3220
  · change upperPayment 3221 ≤ upperValue ((point split endpoint 4096 3221+point split endpoint 4096 3222)/2)
    have hp : upperPayment 3221 = (132345197166:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3221+point split endpoint 4096 3222)/2 = (657172277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657172277:ℝ)/168755200)*ClassicalSixthBranch.v ((657172277:ℝ)/168755200)/ClassicalSixthBranch.r = (89656022756105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3221
  · change upperPayment 3222 ≤ upperValue ((point split endpoint 4096 3222+point split endpoint 4096 3223)/2)
    have hp : upperPayment 3222 = (132210059770:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3222+point split endpoint 4096 3223)/2 = (657197427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657197427:ℝ)/168755200)*ClassicalSixthBranch.v ((657197427:ℝ)/168755200)/ClassicalSixthBranch.r = (89636526999225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3222
  · change upperPayment 3223 ≤ upperValue ((point split endpoint 4096 3223+point split endpoint 4096 3224)/2)
    have hp : upperPayment 3223 = (132074887985:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3223+point split endpoint 4096 3224)/2 = (657222577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657222577:ℝ)/168755200)*ClassicalSixthBranch.v ((657222577:ℝ)/168755200)/ClassicalSixthBranch.r = (89617033266417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3223
  · change upperPayment 3224 ≤ upperValue ((point split endpoint 4096 3224+point split endpoint 4096 3225)/2)
    have hp : upperPayment 3224 = (131939681802:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3224+point split endpoint 4096 3225)/2 = (657247727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657247727:ℝ)/168755200)*ClassicalSixthBranch.v ((657247727:ℝ)/168755200)/ClassicalSixthBranch.r = (89597541557681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3224
  · change upperPayment 3225 ≤ upperValue ((point split endpoint 4096 3225+point split endpoint 4096 3226)/2)
    have hp : upperPayment 3225 = (131804441212:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3225+point split endpoint 4096 3226)/2 = (657272877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657272877:ℝ)/168755200)*ClassicalSixthBranch.v ((657272877:ℝ)/168755200)/ClassicalSixthBranch.r = (89578051873017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3225
  · change upperPayment 3226 ≤ upperValue ((point split endpoint 4096 3226+point split endpoint 4096 3227)/2)
    have hp : upperPayment 3226 = (131669166208:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3226+point split endpoint 4096 3227)/2 = (657298027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657298027:ℝ)/168755200)*ClassicalSixthBranch.v ((657298027:ℝ)/168755200)/ClassicalSixthBranch.r = (89558564212425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3226
  · change upperPayment 3227 ≤ upperValue ((point split endpoint 4096 3227+point split endpoint 4096 3228)/2)
    have hp : upperPayment 3227 = (131533856780:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3227+point split endpoint 4096 3228)/2 = (657323177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657323177:ℝ)/168755200)*ClassicalSixthBranch.v ((657323177:ℝ)/168755200)/ClassicalSixthBranch.r = (89539078575905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3227
  · change upperPayment 3228 ≤ upperValue ((point split endpoint 4096 3228+point split endpoint 4096 3229)/2)
    have hp : upperPayment 3228 = (131398512920:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3228+point split endpoint 4096 3229)/2 = (657348327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657348327:ℝ)/168755200)*ClassicalSixthBranch.v ((657348327:ℝ)/168755200)/ClassicalSixthBranch.r = (89519594963457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3228
  · change upperPayment 3229 ≤ upperValue ((point split endpoint 4096 3229+point split endpoint 4096 3230)/2)
    have hp : upperPayment 3229 = (131263134620:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3229+point split endpoint 4096 3230)/2 = (657373477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657373477:ℝ)/168755200)*ClassicalSixthBranch.v ((657373477:ℝ)/168755200)/ClassicalSixthBranch.r = (89500113375081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3229
  · change upperPayment 3230 ≤ upperValue ((point split endpoint 4096 3230+point split endpoint 4096 3231)/2)
    have hp : upperPayment 3230 = (131127721871:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3230+point split endpoint 4096 3231)/2 = (657398627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657398627:ℝ)/168755200)*ClassicalSixthBranch.v ((657398627:ℝ)/168755200)/ClassicalSixthBranch.r = (89480633810777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3230
  · change upperPayment 3231 ≤ upperValue ((point split endpoint 4096 3231+point split endpoint 4096 3232)/2)
    have hp : upperPayment 3231 = (130992274665:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3231+point split endpoint 4096 3232)/2 = (657423777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((657423777:ℝ)/168755200)*ClassicalSixthBranch.v ((657423777:ℝ)/168755200)/ClassicalSixthBranch.r = (89461156270545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3231
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_201
